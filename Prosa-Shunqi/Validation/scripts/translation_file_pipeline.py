#!/usr/bin/env python3
"""Spec-driven fresh prepare / check / fail-closed publication of one
authoritative Prosa v0.6 source file.

It factors the per-file validate_*.sh / publish_*.py pattern used since
Rank 82 into one tool driven by a JSON spec under
Validation/tooling/file_specs/<slug>.json:

  prepare  accepted dependency closure (hash-checked against the dependency
           manifests) + source binding (byte-identical pinned source, audited
           proof-only patch, or extract_v06_semantic_source.py) + type
           fingerprint probe + fresh Lean build + Lean type/axiom audit
           + actual lean4export + Rocq import
  check    imported-symbol preflight, certificate chain compile, imported type
           audit, fail-closed Lean axiom audit and Rocq assumption audit
  publish  manifest / status / publication directory (hash-chained to the
           previous status); refuses on any failed gate

The production target is always built fresh.  A computation fixture .olean is
reused from the content-addressed cache (.work/cache/lean_fixtures) only when
its key matches: fixture source bytes, Lean binary/version/options, the Lake
manifest, and the sha256 of every Prosa/Validation .olean in its actual import
closure (read from the compiled import tables).  PIPELINE_FIXTURE_CACHE=0
builds every fixture fresh (clean path).  Certificate modules are compiled in
chain order; a module is reused within the same run only when its checkpoint
key (Rocq/importer identity, imported .vo, source .vo set, its own .v and the
previous module's .vo) and its recorded .vo/log hashes all match.

Usage: translation_file_pipeline.py <spec.json> prepare|check|publish|all
"""

from __future__ import annotations

import csv
import difflib
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
from datetime import datetime, timezone
from pathlib import Path

PROJECT = Path(__file__).resolve().parents[2]
ROOT = PROJECT.parent
V = PROJECT / "Validation"
PIPE = V / "planning/v06_pipeline"
DEP = V / "planning/v06_dependency"
EXP = V / ".work/experiments"
IMPORTER = V / ".work/tooling/rocq-lean-import/src"
SOURCE_ROOT = V / ".work/prosa-v06-414e667"
PIN = "414e66760333eaa4ef78c685bcf53291c527a548"
TREE = "7d7e94c731f7eefde4ca738310d4cafdd7bebdf0"
PACKAGES = ["mathlib", "plausible", "proofwidgets", "batteries", "aesop", "importGraph",
            "LeanSearchClient", "Qq", "Cli"]
ESCAPE_ROCQ = re.compile(r"\b(Admitted|admit|Axiom|Parameter)\b")
ESCAPE_LEAN = re.compile(r"\b(sorry|admit|axiom|unsafe)\b", re.I)

# ------------------------------------------------------------------ validation family
# "v06" (the default) is the pinned Prosa v0.6 chain above.  "classic" is opt-in (spec field
# `family: "classic"`, Stage 0 of classic-prosa/casestudy-translation, approved by the user on
# 2026-10-01): ProsaBuddy's classic Prosa at commit f692cb7 (the case-study environment), its own
# planning inputs (planning/classic_dependency), its own status chain (planning/classic_pipeline)
# and acceptance labels, and the recorded Rocq 9.0 compatibility prelude for classic source files.
# Accepted v0.6 artifacts a classic run reuses are checked against the v0.6 manifests.  Every value
# below keeps its v0.6 meaning unless `configure_family` switches it for a classic spec.
FAMILY = "v06"
V06_PIPE = PIPE
ACCEPT_FILE, ACCEPT_DECL = "ACCEPTED_V06_FILE", "ACCEPTED_V06_TRANSLATION"
PUBLISH_DIR = V / "imported/translation_order"
SLICE_PREFIX = "TRANSLATION_ORDER_"
AUTHORITATIVE = {"files": 357, "declarations": 2439}
CLASSIC_PRELUDE: list[str] = []
CLASSIC = {
    "source_root": V / ".work/prosabuddy-f692cb7/prosaworkspace",
    "pin": "f692cb7479780cf6009493f373a309e13165201c",
    "tree": "24727b135eda27b7234119bf8d931d962d7c3593",
    "pipe": V / "planning/classic_pipeline",
    "dep": V / "planning/classic_dependency",
    # opt-in `classic_scope: "full"` (comprehensive classic validation, 2026-10-03): the planning inputs of the
    # whole classic folder (scripts/classic_full_reference_evidence.py); specs without the field are unchanged
    "full_dep": V / "planning/classic_full_dependency",
    "prelude_source": PROJECT / "classic-prosa/rocq93-port/Rocq90Compat.v",
    "prelude_sha256": "",   # bound at configuration time to planning/classic_dependency/prelude.json
}


def configure_family(spec: "Spec") -> None:
    global FAMILY, PIPE, DEP, SOURCE_ROOT, PIN, TREE, ACCEPT_FILE, ACCEPT_DECL, PUBLISH_DIR, SLICE_PREFIX
    family = spec.get("family", "v06")
    require(family in ("v06", "classic"), f"unknown family {family}", spec.tag)
    if family == "v06":
        return
    require(not spec.get("coqeal"), "classic family has no CoqEAL", spec.tag)
    FAMILY = "classic"
    PIPE, DEP, SOURCE_ROOT = CLASSIC["pipe"], CLASSIC["dep"], CLASSIC["source_root"]
    require(spec.get("classic_scope") in (None, "full"), "unknown classic_scope", spec.tag)
    if spec.get("classic_scope") == "full":
        DEP = CLASSIC["full_dep"]
    PIN, TREE = CLASSIC["pin"], CLASSIC["tree"]
    ACCEPT_FILE, ACCEPT_DECL = "ACCEPTED_CLASSIC_FILE", "ACCEPTED_CLASSIC_TRANSLATION"
    PUBLISH_DIR = V / "imported/classic_translation_order"
    SLICE_PREFIX = "CLASSIC_TRANSLATION_ORDER_"
    scope = read(DEP / "scope.json")
    AUTHORITATIVE.update(files=scope["case_study_files"], declarations=scope["case_study_declarations"])
    prelude = read(DEP / "prelude.json")
    require(sha(CLASSIC["prelude_source"]) == prelude["sha256"], "compatibility prelude changed", spec.tag)
    CLASSIC["prelude_sha256"] = prelude["sha256"]
    ROCQ_EXTRA[:] = ["-Q", str(spec.work / "compat"), "Compat"]
    CLASSIC_PRELUDE[:] = ["-ri", "Compat.Rocq90Compat"]


def source_flags(rel: str) -> list[str]:
    """Extra compile flags of one source file: the recorded prelude for classic files of a classic run."""
    return CLASSIC_PRELUDE if FAMILY == "classic" and rel.startswith("classic/") else []


def cert_name(declaration: str) -> str:
    """Default principal certificate name (a classic declaration name may carry its Rocq module path)."""
    return f"{declaration.replace('.', '_')}_correspondence"


class Rejected(SystemExit):
    pass


def require(cond: bool, msg: str, tag: str = "PIPELINE") -> None:
    if not cond:
        raise Rejected(f"{tag}_REJECTED: {msg}")


def ssr_fun_body_unparen(text: str) -> str:
    """Rocq 9.0 (official evidence) prints a lambda that is the body of ssreflect's `fun=>` (`fun _ => ...`)
    with parentheses (`fun=> (fun R : T => e)`, also when that body is itself a wildcard lambda:
    `fun=> (fun=> (fun R : T => e))`); Rocq 9.3 (the validation toolchain) prints the same term without them.
    Remove exactly those parentheses, nothing else."""
    while True:
        openers = [k for k in (text.find("fun=> (fun "), text.find("fun=> (fun=>")) if k >= 0]
        if not openers:
            return text
        start, depth, close = min(openers) + 6, 0, None
        for k in range(start, len(text)):
            depth += {"(": 1, ")": -1}.get(text[k], 0)
            if depth == 0:
                close = k
                break
        if close is None:
            return text
        text = text[:start] + text[start + 1:close] + text[close + 1:]


def sha(path: Path) -> str:
    require(path.is_file() and path.stat().st_size > 0, f"missing/empty {path}")
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _manifest_entries(obj):
    """All dict entries (recursively) of an accepted manifest."""
    if isinstance(obj, dict):
        yield obj
        for v in obj.values():
            yield from _manifest_entries(v)
    elif isinstance(obj, list):
        for v in obj:
            yield from _manifest_entries(v)


def read(path: Path):
    return json.loads(path.read_text())


def git(repo: Path, *args: str) -> str:
    return subprocess.check_output(["git", "-C", str(repo), *args], text=True).strip()


def run(cmd: list[str], log: Path, cwd: Path, env=None, append=False) -> int:
    # `ulimit -s 65520` as in the shell validators (deep imports / kernel checks)
    wrapped = ["zsh", "-c", 'ulimit -s 65520 && exec "$@"', "_", *cmd]
    with log.open("a" if append else "w") as out:
        return subprocess.run(wrapped, cwd=cwd, env=env, stdout=out, stderr=subprocess.STDOUT).returncode


# Opt-in extra Rocq load path: set only for a spec with a `coqeal` field (the implementation/refinements files);
# empty for every other spec, whose Rocq commands are therefore unchanged.
ROCQ_EXTRA: list[str] = []


def rocq(args: list[str], log: Path, cwd: Path, append=False) -> int:
    return run(["opam", "exec", "--switch=rocq93rc1", "--", "rocq", "c", *ROCQ_EXTRA, *args], log, cwd,
               append=append)


def lean_env(olean: Path) -> dict:
    env = dict(os.environ)
    env["LEAN_PATH"] = ":".join([str(olean)] + [
        str(PROJECT / f".lake/packages/{p}/.lake/build/lib/lean") for p in PACKAGES])
    env["ELAN_TOOLCHAIN"] = "leanprover/lean4:v4.33.1"
    return env


def accepted_status(source_file: str) -> str:
    chains = [(PIPE, ACCEPT_FILE)] + ([(V06_PIPE, "ACCEPTED_V06_FILE")] if FAMILY == "classic" else [])
    for pipe, label in chains:
        for path in sorted(pipe.glob("*status.json")):
            try:
                item = read(path).get("per_file", {}).get(source_file)
            except json.JSONDecodeError:
                continue
            if isinstance(item, dict) and item.get("status") == label:
                return path.name if FAMILY == "v06" else f"{pipe.name}/{path.name}"
    raise Rejected(f"PIPELINE_REJECTED: dependency not accepted: {source_file}")


def v06_file_olean_hash(source_file: str) -> str:
    """Classic runs only: the olean hash recorded for an accepted v0.6 file by the publication that accepted it
    (module manifests: `production_olean_sha256`; the early slice manifests: `files[f].fresh_olean_sha256` or the
    per-declaration `fresh_olean_sha256`, which must agree)."""
    require(FAMILY == "classic", "v06_file olean artifacts are a classic-run feature")
    status = accepted_status(source_file)
    require(status.startswith(V06_PIPE.name + "/"), f"{source_file} is not accepted by the v0.6 chain")
    name = status.split("/", 1)[1]
    man = read(V06_PIPE / (name[:-len("status.json")] + "manifest.json"))
    found: set[str] = set()
    if man.get("source_file") == source_file and man.get("production_olean_sha256"):
        found.add(man["production_olean_sha256"])
    if isinstance(man.get("files"), dict) and isinstance(man["files"].get(source_file), dict):
        found.add(man["files"][source_file].get("fresh_olean_sha256"))
    for entry in _manifest_entries(man):
        if entry.get("source_file") == source_file and entry.get("fresh_olean_sha256"):
            found.add(entry["fresh_olean_sha256"])
    found.discard(None)
    require(len(found) == 1 and len(next(iter(found))) == 64,
            f"no unique accepted olean hash for {source_file}: {sorted(found)}")
    return next(iter(found))


def extra_olean_hash(art: dict) -> str:
    return v06_file_olean_hash(art["v06_file"]) if art.get("v06_file") else manifest_hash(art["manifest"], art["key"])


def manifest_hash(stem: str, key: str) -> str:
    path, label = PIPE / f"{stem}_module_manifest.json", ACCEPT_FILE
    if FAMILY == "classic" and not path.is_file():   # an accepted v0.6 artifact reused by a classic run
        path, label = V06_PIPE / f"{stem}_module_manifest.json", "ACCEPTED_V06_FILE"
    man = read(path)
    require(man.get("acceptance") == label, f"{stem} not accepted")
    value = man
    for part in key.split("."):  # older manifests keep hashes under artifact_hashes
        if isinstance(value, list) and part.isdigit():  # or inside declarations[i]
            value = value[int(part)] if int(part) < len(value) else None
        else:
            value = value.get(part) if isinstance(value, dict) else None
    require(isinstance(value, str) and len(value) == 64, f"{stem} has no {key}")
    return value


class Spec:
    def __init__(self, path: Path):
        self.path = path
        self.d = read(path)
        d = self.d
        self.tag = d["tag"]
        self.slug = d["slug"]
        self.source = d["source"]
        # opt-in (amendments of an accepted file): a separate run directory, so the accepted run is left untouched
        self.work = EXP / f"{self.slug}{d['amendment']['work_suffix']}" if d.get("amendment") else EXP / f"{self.slug}_final"
        self.cert_dir = V / d["cert_dir"]
        self.fixtures = "Validation/fixtures/translation_order"

    def __getitem__(self, key):
        return self.d[key]

    def get(self, key, default=None):
        return self.d.get(key, default)


LOCAL_INVENTORY = "local_declaration_inventory.csv"
LOCAL_EVIDENCE = "local_declaration_type_evidence.json"


def inventory(spec: Spec) -> list[dict]:
    with (DEP / "declaration_inventory.csv").open() as stream:
        rows = [r for r in csv.DictReader(stream) if r["source_file"] == spec.source]
    # opt-in (v0.6 specs, user decision 2026-10-04): source-`Local` lemmas, which the authoritative inventory omits,
    # certified like the inventory declarations.  Their rows and official-toolchain `Check` evidence are recorded in
    # the separate files LOCAL_INVENTORY / LOCAL_EVIDENCE (scripts/elaborate_local_declaration_types.py); the
    # authoritative inventory and evidence files are not modified.
    local = spec.get("local_declarations", [])
    if local:
        require(FAMILY == "v06", "local_declarations is a v0.6 feature", spec.tag)
        with (DEP / LOCAL_INVENTORY).open() as stream:
            extra = [r for r in csv.DictReader(stream) if r["source_file"] == spec.source
                     and r["declaration_name"] in local]
        require(sorted(r["declaration_name"] for r in extra) == sorted(local)
                and not {r["declaration_name"] for r in rows} & set(local),
                "local declarations not uniquely recorded in the local inventory", spec.tag)
        rows = sorted(rows + extra, key=lambda r: int(r["source_line"]))
    return rows


def type_evidence(spec: Spec) -> dict:
    """`Check` evidence by qualified name: the authoritative file, plus (opt-in) the recorded evidence of this
    spec's local declarations."""
    evidence = dict(read(DEP / "declaration_type_evidence.json"))
    local = spec.get("local_declarations", [])
    if local:
        recorded = read(DEP / LOCAL_EVIDENCE)["declarations"]
        for r in inventory(spec):
            if r["declaration_name"] in local:
                item = recorded.get(r["qualified_name"])
                require(item is not None and item["source_file"] == spec.source
                        and r["final_type_or_type_fingerprint"] == "rocq-check-sha256:" + item["sha256"]
                        and r["qualified_name"] not in evidence,
                        f"local declaration evidence not bound to its inventory row: {r['qualified_name']}", spec.tag)
                evidence[r["qualified_name"]] = item
    return evidence


def stamp(spec: Spec, stage: str, seconds: float, mode: str = "FRESH") -> None:
    with (spec.work / "stage_timing.tsv").open("a") as out:
        out.write(f"{stage}\t{mode}\t{int(seconds)}\n")


def digest(obj) -> str:
    return hashlib.sha256(json.dumps(obj, sort_keys=True).encode()).hexdigest()


# --------------------------------------------------------------------------- fixture cache

FIXTURE_CACHE = V / ".work/cache/lean_fixtures"
LEAN_OPTIONS = ["-DautoImplicit=false", "-R", str(PROJECT)]


def lean_identity(env: dict) -> dict:
    """Everything outside the Prosa/Validation import closure that a fixture .olean depends on."""
    prefix = Path(subprocess.check_output(["lean", "--print-prefix"], env=env, text=True).strip())
    return {"lean_binary_sha256": sha(prefix / "bin/lean"),
            "lean_version": subprocess.check_output(["lean", "--version"], env=env, text=True).strip(),
            "lake_manifest_sha256": sha(PROJECT / "lake-manifest.json"),
            "lean_toolchain": (PROJECT / "lean-toolchain").read_text().strip(),
            "options": LEAN_OPTIONS, "lean_path_packages": PACKAGES}


def olean_import_tables(files: list[Path], env: dict, tag: str) -> dict[str, list[str]]:
    """module -> imported modules, read from the compiled .olean files themselves."""
    if not files:
        return {}
    proc = subprocess.run(["lean", "--run", str(V / "scripts/olean_imports.lean"), *map(str, files)],
                          env=env, cwd=PROJECT, capture_output=True, text=True)
    require(proc.returncode == 0, f"olean import table read failed: {proc.stderr[-500:]}", tag)
    by_path = dict(line.split("\t", 1) for line in proc.stdout.splitlines() if "\t" in line)
    require(len(by_path) == len(files), "olean import table incomplete", tag)
    return {str(p): by_path[str(p)].split() for p in files}


def olean_module(olean: Path, path: Path) -> str:
    return ".".join(path.relative_to(olean).with_suffix("").parts)


def source_imports(path: Path) -> list[str]:
    """Header imports of a fixture source (checked against the built .olean afterwards)."""
    mods: list[str] = []
    text = path.read_text()
    while True:  # comments may precede the header, as in Lean (`--`, `/- … -/`, `/-! … -/`, nested)
        text = text.lstrip()
        if text.startswith("--"):
            text = text.split("\n", 1)[1] if "\n" in text else ""
        elif text.startswith("/-"):
            depth, i = 0, 0
            while i < len(text):
                if text.startswith("/-", i):
                    depth, i = depth + 1, i + 2
                elif text.startswith("-/", i):
                    depth, i = depth - 1, i + 2
                    if depth == 0:
                        break
                else:
                    i += 1
            text = text[i:]
        elif text.startswith("import "):
            line, _, text = text.partition("\n")
            mods += line.split("--")[0].split()[1:]
        else:
            return mods


def fsha(path: Path) -> str:
    """sha256 of an existing (possibly empty) file."""
    return hashlib.sha256(path.read_bytes()).hexdigest()


def fixture_cache_hit(entry: Path, module: str, key: str) -> bool:
    meta_path, cached = entry / "meta.json", entry / f"{module}.olean"
    if not (meta_path.is_file() and cached.is_file()):
        return False
    try:
        meta = read(meta_path)
    except json.JSONDecodeError:
        return False
    return (meta.get("key") == key and meta.get("module") == module
            and fsha(cached) == meta.get("olean_sha256"))


def fixture_cache_store(entry: Path, module: str, key: str, built: Path, slug: str) -> None:
    import time
    FIXTURE_CACHE.mkdir(parents=True, exist_ok=True)
    if entry.exists():
        if fixture_cache_hit(entry, module, key):  # stored meanwhile by a concurrent run
            return
        entry.rename(entry.with_name(f"{entry.name}.invalid-{int(time.time())}"))  # kept as evidence
    tmp = Path(tempfile.mkdtemp(dir=FIXTURE_CACHE, prefix=".tmp-"))
    shutil.copy2(built, tmp / f"{module}.olean")
    (tmp / "meta.json").write_text(json.dumps({
        "module": module, "key": key, "olean_sha256": sha(built), "built_in_run": slug,
        "created_at": datetime.now(timezone.utc).isoformat()}, indent=2) + "\n")
    try:
        tmp.rename(entry)
    except OSError:  # a concurrent run stored the same key first
        shutil.rmtree(tmp)


def build_fixtures(spec: Spec, olean: Path, env: dict) -> None:
    """Build (or reuse from the verified cache) every computation fixture, timing each one."""
    import time
    tag, work = spec.tag, spec.work
    use_cache = os.environ.get("PIPELINE_FIXTURE_CACHE", "1") != "0"
    identity = lean_identity(env)
    fixture_dir = olean / "Validation/fixtures/translation_order"
    compiled = sorted(olean.rglob("*.olean"))  # production + accepted dependencies
    tables = {olean_module(olean, Path(p)): imps
              for p, imps in olean_import_tables(compiled, env, tag).items()}
    hashes: dict[str, str] = {}

    def olean_sha(module: str) -> str:
        if module not in hashes:
            path = olean / (module.replace(".", "/") + ".olean")
            hashes[module] = fsha(path) if path.is_file() else "MISSING"
        return hashes[module]

    fixture_imports: dict[str, list[str]] = {}
    provenance: dict = {"identity": identity, "cache_enabled": use_cache, "fixtures": {}}
    for module in spec.get("fixtures", []):
        t1 = time.time()
        source = PROJECT / spec.fixtures / f"{module}.lean"
        name = f"Validation.fixtures.translation_order.{module}"
        fixture_imports[name] = source_imports(source)
        closure: set[str] = set()
        stack = list(fixture_imports[name])
        while stack:
            m = stack.pop()
            if m in closure or not m.startswith(("Prosa.", "Validation.")):
                continue
            closure.add(m)
            stack += fixture_imports.get(m, tables.get(m, []))
        key = digest({"format": 1, "module": name, "source_sha256": sha(source), "identity": identity,
                      "imports": {m: olean_sha(m) for m in sorted(closure)}})
        out = fixture_dir / f"{module}.olean"
        entry = FIXTURE_CACHE / key
        if use_cache and fixture_cache_hit(entry, module, key):
            shutil.copy2(entry / f"{module}.olean", out)
            require(sha(out) == read(entry / "meta.json")["olean_sha256"], f"cached fixture copy differs: {module}", tag)
            mode = "CACHED"
        else:
            require(run(["lean", *LEAN_OPTIONS, "-o", str(out), f"{spec.fixtures}/{module}.lean"],
                        work / f"{module}_build.log", PROJECT, env) == 0, f"fixture build failed: {module}", tag)
            if use_cache:
                fixture_cache_store(entry, module, key, out, spec.slug)
            mode = "FRESH"
        hashes[name] = sha(out)
        provenance["fixtures"][module] = {"mode": mode, "key": key, "olean_sha256": hashes[name],
                                          "import_closure": len(closure)}
        stamp(spec, f"fixture:{module}", time.time() - t1, mode)
    # the keys used the source header imports: they must be what each built/reused .olean records
    built = [fixture_dir / f"{m}.olean" for m in spec.get("fixtures", [])]
    for path, imps in olean_import_tables(built, env, tag).items():
        name = olean_module(olean, Path(path))
        require(sorted(set(imps) - {"Init"}) == sorted(set(fixture_imports[name]) - {"Init"}),
                f"fixture .olean imports differ from its header: {name}", tag)
    (work / "lean_fixture_provenance.json").write_text(json.dumps(provenance, indent=2) + "\n")


# ------------------------------------------------------------------ official proof closure

def official_closure_files(spec: Spec) -> tuple[list[str], set[str]]:
    """The recorded official proof closure (dependency order, the module last) and the files its recorded
    compatibility patches touch (never the module itself)."""
    closure = (V / spec["official_closure"]["files"]).read_text().split()
    require(closure[-1] == spec.source and len(set(closure)) == len(closure), "closure list malformed", spec.tag)
    patched: set[str] = set()
    for patch in spec["official_closure"]["patches"]:
        touched = re.findall(r"^\+\+\+ b/(\S+)", (V / patch).read_text(), re.M)
        require(all(t in closure for t in touched), f"patch touches a file outside the closure: {patch}", spec.tag)
        # opt-in (`module_change`): the module may receive exactly the file-local rewrite-order flag, checked
        # line by line in `module_flag_only`; every other spec keeps the module unpatched
        # opt-in `proof_only_patch` (user decision 2026-10-03, classic rank 172): the module may receive a recorded
        # patch that changes only proof scripts, checked in `module_proof_only`
        require(spec.source not in touched
                or spec["official_closure"].get("module_change") in ("rewrite_goals_order_flag", "proof_only_patch"),
                "the module itself must not be patched", spec.tag)
        patched |= set(touched)
    return closure, patched


REWRITE_ORDER_FLAG = "Set SsrOldRewriteGoalsOrder."
# the only files whose certificates may use Rocq functional extensionality (user decision 2026-10-03)
FUNEXT_FILES = {"classic/model/schedule/uni/sustainability.v",
                "classic/analysis/uni/susp/sustainability/allcosts/main_claim.v"}


PROOF_START = re.compile(r"^\s*Proof\b[^.]*\.\s*$")
PROOF_END = re.compile(r"^\s*(Qed|Defined)\.\s*$")
PROOF_FORBIDDEN = re.compile(r"\b(Admitted|admit|Abort|Axiom|Axioms|Parameter|Parameters|Conjecture|Hypothesis)\b")


def _proof_interiors_blanked(lines: list[str]) -> list[str]:
    out, inside = [], False
    for line in lines:
        if inside:
            if PROOF_END.match(line):
                inside = False
                out.append(line)
            continue
        out.append(line)
        if PROOF_START.match(line):
            inside = True
            out.append("(* proof script *)")
    return out


def module_proof_only(official: Path, compiled: Path) -> bool:
    """`compiled` differs from `official` only inside proof scripts: with every proof interior (the lines between a
    `Proof.` line and its `Qed.`/`Defined.` line) blanked the two files are identical, and no changed or added line
    contains `Admitted`, `admit`, `Abort` or an axiom/parameter command.  Statements, definitions and all other
    vernacular are byte-identical; the statement types are in addition checked against the official evidence."""
    a, b = official.read_text().splitlines(), compiled.read_text().splitlines()
    if _proof_interiors_blanked(a) != _proof_interiors_blanked(b):
        return False
    ops = [op for op in difflib.SequenceMatcher(a=a, b=b, autojunk=False).get_opcodes() if op[0] != "equal"]
    return bool(ops) and not any(PROOF_FORBIDDEN.search(line) for op in ops for line in b[op[3]:op[4]])


def module_flag_only(official: Path, compiled: Path) -> bool:
    """`compiled` is `official` with exactly one added line `Set SsrOldRewriteGoalsOrder.` and nothing else."""
    a, b = official.read_text().splitlines(), compiled.read_text().splitlines()
    ops = [op for op in difflib.SequenceMatcher(a=a, b=b, autojunk=False).get_opcodes() if op[0] != "equal"]
    return (len(ops) == 1 and ops[0][0] == "insert" and ops[0][4] - ops[0][3] == 1
            and b[ops[0][3]] == REWRITE_ORDER_FLAG)


# ------------------------------------------------------------------ CoqEAL (opt-in, refinements files only)

def coqeal_files(spec: Spec) -> tuple[dict, Path]:
    """The recorded CoqEAL release: the clone must be at the recorded commit and every used file must have its
    recorded sha256; no CoqEAL file is patched."""
    m = read(V / spec["coqeal"])
    clone = V / m["clone"]
    require(git(clone, "rev-parse", "HEAD") == m["commit"], "CoqEAL clone not at the recorded commit", spec.tag)
    require(not git(clone, "status", "--porcelain", "--untracked-files=no"), "CoqEAL clone modified", spec.tag)
    for f in m["files"]:
        require(sha(clone / f["path"]) == f["sha256"], f"CoqEAL file changed: {f['path']}", spec.tag)
    return m, clone


def build_coqeal(spec: Spec) -> None:
    """Compile the recorded CoqEAL files, unchanged, under the pinned rocq93rc1 into the run (`coqeal/CoqEAL`)."""
    m, clone = coqeal_files(spec)
    out = spec.work / "coqeal/CoqEAL"
    out.mkdir(parents=True)
    log = spec.work / "coqeal_build.log"
    log.write_text("")
    for f in m["files"]:
        shutil.copy2(clone / f["path"], out / Path(f["path"]).name)
    for f in m["files"]:
        require(run(["opam", "exec", "--switch=rocq93rc1", "--", "rocq", "c", "-Q", str(out), "CoqEAL",
                     str(out / Path(f["path"]).name)], log, spec.work / "coqeal", append=True) == 0,
                f"CoqEAL compile failed: {f['path']}", spec.tag)


def coqeal_record(spec: Spec) -> dict:
    m, clone = coqeal_files(spec)
    out = spec.work / "coqeal/CoqEAL"
    for f in m["files"]:
        require(sha(out / Path(f["path"]).name) == f["sha256"], f"run CoqEAL source changed: {f['path']}", spec.tag)
    return {"manifest": spec["coqeal"], "manifest_sha256": sha(V / spec["coqeal"]), "commit": m["commit"],
            "type_evidence": "planning/v06_dependency/coqeal_declaration_type_evidence.json",
            "type_evidence_sha256": sha(DEP / "coqeal_declaration_type_evidence.json"),
            "vo_sha256": {p.name: sha(p) for p in sorted(out.glob("*.vo"))}}


def build_official_closure(spec: Spec, src: Path, log: Path) -> None:
    """Source tree = the pinned official files of the recorded closure (each hash-checked against the file
    inventory) + the recorded compatibility patches, compiled in dependency order; no accepted semantic module."""
    closure, patched = official_closure_files(spec)
    with (DEP / "file_inventory.csv").open() as stream:
        inv = {r["file"]: r["sha256"] for r in csv.DictReader(stream)}
    for rel in closure:
        require(inv[rel] == sha(SOURCE_ROOT / rel), f"pinned closure file changed: {rel}", spec.tag)
        (src / rel).parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(SOURCE_ROOT / rel, src / rel)
    for patch in spec["official_closure"]["patches"]:
        subprocess.run(["patch", "-s", "-p1", "-i", str(V / patch)], cwd=src, check=True)
    for rel in closure:
        require((sha(src / rel) == sha(SOURCE_ROOT / rel)) == (rel not in patched),
                f"closure file differs from the pinned file without a recorded patch: {rel}", spec.tag)
    if spec.source in patched:
        if spec["official_closure"].get("module_change") == "proof_only_patch":
            require(module_proof_only(SOURCE_ROOT / spec.source, src / spec.source),
                    "module change is not confined to proof scripts", spec.tag)
        else:
            require(module_flag_only(SOURCE_ROOT / spec.source, src / spec.source),
                    "module change is not exactly the rewrite-order flag", spec.tag)
    for rel in closure:
        require(rocq(["-R", str(src), "prosa", *source_flags(rel), rel], log, src, append=True) == 0,
                f"official closure compile failed: {rel}", spec.tag)


# --------------------------------------------------------------------------- prepare

def prepare(spec: Spec) -> None:
    import time
    tag, work = spec.tag, spec.work
    require(not work.exists(), f"{work} exists", tag)
    official = SOURCE_ROOT / spec.source
    with (DEP / "file_inventory.csv").open() as stream:
        row = next(r for r in csv.DictReader(stream) if r["file"] == spec.source)
    require(row["sha256"] == sha(official), "file inventory mismatch", tag)
    # a classic run may start without a base run (no Lean or Rocq dependency artifacts to inherit)
    require(spec["base_run"] is not None or (FAMILY == "classic" and not spec["base_checks"]),
            "base_run required", tag)
    base = EXP / spec["base_run"] if spec["base_run"] is not None else None
    for check in spec["base_checks"]:
        if check.get("olean"):
            require(sha(base / "olean" / check["olean"]) ==
                    manifest_hash(check["manifest"], check.get("olean_key", "production_olean_sha256")),
                    f"base olean changed: {check['olean']}", tag)
        if check.get("vo"):
            require(sha(base / "source" / check["vo"]) ==
                    manifest_hash(check["manifest"], check.get("vo_key", "source_vo_sha256")),
                    f"base source vo changed: {check['vo']}", tag)
    for sub in ("olean/Validation/fixtures/translation_order", "imported", "certificates"):
        (work / sub).mkdir(parents=True)
    if FAMILY == "classic":   # the recorded Rocq 9.0 compatibility prelude, compiled into the run
        (work / "compat").mkdir()
        shutil.copy2(CLASSIC["prelude_source"], work / "compat/Rocq90Compat.v")
        require(sha(work / "compat/Rocq90Compat.v") == CLASSIC["prelude_sha256"], "prelude copy changed", tag)
        require(rocq(["Rocq90Compat.v"], work / "compat/build.log", work / "compat") == 0,
                "compatibility prelude compile failed", tag)
    (work / "stage_timing.tsv").write_text("")
    t0 = time.time()
    if spec.get("coqeal"):
        build_coqeal(spec)

    # ---- source binding
    src = work / "source"
    if spec["source_mode"] == "official_closure" or base is None:   # no inherited tree: built below
        src.mkdir(parents=True)
    else:
        shutil.copytree(base / "source", src)
    for rel in spec.get("extra_pinned_sources", []):
        (src / rel).parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(SOURCE_ROOT / rel, src / rel)
    for art in spec.get("extra_artifacts", []):  # accepted, hash-verified dependency artifacts
        dest = work / art["to"]
        dest.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(EXP / art["from"], dest)
        require(sha(dest) == manifest_hash(art["manifest"], art["key"]), f"artifact changed: {art['to']}", tag)
    for patch in spec.get("extra_source_patches", []):  # approved patches of accepted dependencies
        subprocess.run(["patch", "-s", "-p1", "-i", str(V / patch)], cwd=src, check=True)
    mode = spec["source_mode"]
    log = work / "source_build.log"
    log.write_text("")
    # accepted dependencies bound only by extraction are reached at their logical
    # path through a one-line re-export shim of their accepted semantic module
    # (whose .vo is hash-checked by base_checks), as in the zero-declaration validator
    for dep_rel, module in spec.get("dependency_shims", {}).items():
        shim = src / dep_rel
        require(not shim.exists(), f"shim target already exists: {dep_rel}", tag)
        shim.parent.mkdir(parents=True, exist_ok=True)
        shim.write_text(f"Require Export prosa.{module}.\nExport {module}.\n")
        require(rocq(["-R", str(src), "prosa", dep_rel], log, src, append=True) == 0,
                f"dependency shim failed: {dep_rel}", tag)
    for rel in spec.get("extra_pinned_sources", []):
        require(rocq(["-R", str(src), "prosa", rel], log, src, append=True) == 0,
                f"extra pinned source failed: {rel}", tag)
    for rel, (stem, key) in spec.get("extra_source_vo_checks", {}).items():
        require(sha(src / rel) == manifest_hash(stem, key), f"extra source .vo changed: {rel}", tag)
    # accepted generated (definition-extraction) validation sources of accepted
    # files whose pinned proofs do not build in this toolchain: the .v is copied
    # from its accepted run, its sha256 must equal the `validation_source_sha256`
    # recorded for that source file in the accepted manifest, and it is compiled
    for gen in spec.get("extra_generated_sources", []):
        entries = [e for e in _manifest_entries(read(PIPE / gen["manifest_file"]))
                   if e.get("source_file") == gen["source_file"]
                   and e.get("file_status") == "ACCEPTED_V06_FILE"]
        require(len(entries) == 1, f"no unique accepted manifest entry: {gen['source_file']}", tag)
        require(entries[0].get("validation_source_file") == Path(gen["to"]).name,
                f"validation source name differs: {gen['to']}", tag)
        dest = src / gen["to"]
        require(not dest.exists(), f"generated source target exists: {gen['to']}", tag)
        shutil.copy2(V / gen["from"], dest)
        require(sha(dest) == entries[0].get("validation_source_sha256"),
                f"generated source changed: {gen['to']}", tag)
        require(rocq(["-R", str(src), "prosa", gen["to"]], log, src, append=True) == 0,
                f"generated source failed: {gen['to']}", tag)
    probe_args: list[str]
    if mode in ("pinned", "patched"):
        (src / spec.source).parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(official, src / spec.source)
        for patch in spec.get("patches", []):
            subprocess.run(["patch", "-s", "-p1", "-i", str(V / patch)], cwd=src, check=True)
        require(rocq(["-R", str(src), "prosa", *source_flags(spec.source), spec.source], log, src,
                     append=True) == 0, "official source compile failed", tag)
        require(rocq(["-R", str(src), "prosa", str(PROJECT / spec["fingerprint_probe"])],
                     work / "source_type_fingerprint.log", src) == 0, "fingerprint probe failed", tag)
    elif mode == "official_closure":
        build_official_closure(spec, src, log)
        require(rocq(["-R", str(src), "prosa", str(PROJECT / spec["fingerprint_probe"])],
                     work / "source_type_fingerprint.log", src) == 0, "fingerprint probe failed", tag)
    elif mode == "extract":
        x = spec["extraction"]
        names = [r["declaration_name"] for r in inventory(spec)]
        # source-local helper blocks (e.g. #[local] instances) that the statements mention;
        # they must be byte-identical computational blocks (checked at publication)
        helper_blocks = x.get("helper_blocks", [])
        names = helper_blocks + names
        evidence_path = DEP / "declaration_type_evidence.json"
        if spec.get("local_declarations"):   # opt-in: authoritative evidence + the recorded local evidence
            evidence_path = work / "type_evidence_with_local.json"
            evidence_path.write_text(json.dumps(type_evidence(spec), indent=2, sort_keys=True) + "\n")
        cmd = [sys.executable, str(V / "scripts/extract_v06_semantic_source.py"),
               "--source-root", str(SOURCE_ROOT), "--source-file", spec.source,
               "--module", x["module"], "--declarations", ",".join(names),
               "--elaborated-evidence", str(evidence_path),
               "--qualified-prefix", "prosa." + spec.source[:-2].replace("/", "."),
               "--output", str(src / f"{x['module']}.v"),
               "--metadata", str(work / "source_extraction.json")]
        if spec.get("computational") or helper_blocks:
            cmd += ["--computational", ",".join(helper_blocks + spec.get("computational", []))]
        if spec.get("type_valued"):
            cmd += ["--type-valued", ",".join(spec["type_valued"])]
        for flag, key in (("--drop-import", "drop_imports"), ("--add-import", "add_imports"),
                          ("--printer-repair", "printer_repairs"), ("--local-binding", "local_bindings")):
            for item in x.get(key, []):
                cmd += [flag, item]
        if x.get("source_order"):
            cmd.append("--source-order")
        if spec.get("local_declarations"):
            cmd += ["--local-declarations", ",".join(spec["local_declarations"])]
        if x.get("self_named_instance_context"):
            cmd.append("--self-named-instance-context")
        for item in x.get("omit_context_lets", []):
            cmd += ["--omit-context-let", item]
        for item in x.get("body_parenthesizations", []):
            cmd += ["--body-parenthesization", "\t".join((item["name"], item["old"], item["new"]))]
        if x.get("omit_theorem_context", True):
            cmd.append("--omit-theorem-context-when-elaborated")
        require(run(cmd, work / "source_extraction.log", PROJECT) == 0, "extraction failed", tag)
        shutil.copy2(PROJECT / spec["fingerprint_probe"], src)
        flog = work / "source_type_fingerprint.log"
        flog.write_text("")
        for f in (f"{x['module']}.v", Path(spec["fingerprint_probe"]).name):
            require(rocq(["-R", str(src), "prosa", f], flog, src, append=True) == 0,
                    f"semantic source compile failed: {f}", tag)
    else:
        raise Rejected(f"{tag}_REJECTED: unknown source_mode {mode}")
    stamp(spec, "source_acquisition", time.time() - t0)
    t0 = time.time()

    # ---- Lean
    olean = work / "olean"
    if base is not None:
        shutil.copytree(base / "olean/Prosa", olean / "Prosa")
    else:
        (olean / "Prosa").mkdir(parents=True)
    for art in spec.get("extra_olean_artifacts", []):
        dest = olean / art["to"]
        dest.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(EXP / art["from"], dest)
        require(sha(dest) == extra_olean_hash(art), f"olean artifact changed: {art['to']}", tag)
    env = lean_env(olean)
    for lean_src, out, stem, *key in spec.get("extra_lean", []):
        (olean / out).parent.mkdir(parents=True, exist_ok=True)
        require(run(["lean", "-DautoImplicit=false", "-R", str(PROJECT), "-o", str(olean / out), lean_src],
                    work / "extra_lean_build.log", PROJECT, env, append=True) == 0,
                f"extra Lean build failed: {lean_src}", tag)
        if stem:
            require(sha(olean / out) == manifest_hash(stem, key[0] if key else "production_olean_sha256"),
                    f"rebuilt dependency olean differs from its manifest: {out}", tag)
    prod_out = olean / spec["production_olean"]
    prod_out.parent.mkdir(parents=True, exist_ok=True)
    t1 = time.time()
    require(run(["lean", *LEAN_OPTIONS, "-o", str(prod_out), spec["production"]],
                work / "lean_build.log", PROJECT, env) == 0, "production Lean build failed", tag)
    stamp(spec, "lean_production", time.time() - t1)
    build_fixtures(spec, olean, env)
    t1 = time.time()
    require(run(["lean", *LEAN_OPTIONS, spec["lean_type_audit"]],
                work / "lean_type_audit.log", PROJECT, env) == 0, "Lean type audit failed", tag)
    stamp(spec, "lean_type_audit", time.time() - t1)
    stamp(spec, "lean_build", time.time() - t0)
    t0 = time.time()

    # ---- export / import
    name = spec["export_name"]
    export_env = dict(env)
    # optional exporter switches recorded in the spec (e.g. keep theorem types
    # un-reduced when a kernel-guarded Finset.Ico projection is configured)
    # LEAN4EXPORT_NAT_INDEX_ALIASES: reducible aliases of Nat accepted as Finset.Ico sum index types by the
    # projector (planning/classic_policy/tool_changes.md; still kernel-guarded in the export root)
    allowed_export_env = {"LEAN4EXPORT_PRESERVE_REDUCIBLE_THEOREM_TYPES", "LEAN4EXPORT_NAT_INDEX_ALIASES"}
    for k, v in spec.get("export_env", {}).items():
        require(k in allowed_export_env, f"export_env key not allowed: {k}", tag)
        export_env[k] = v
    require(run(["bash", "Validation/scripts/export_actual_artifact.sh", "--config", spec["export_config"],
                 "--output", str(work / f"imported/{name}.out"), "--log", str(work / "export.log"),
                 "--metadata", str(work / "export_metadata.json")], work / "export_driver.log", PROJECT, export_env) == 0,
            "export failed", tag)
    stamp(spec, "export", time.time() - t0)
    t0 = time.time()
    imp = work / "imported"
    for f in ("Subadditivity.out", "ImportedSubadditivity.v"):
        shutil.copy2(V / "imported/foundation_slice_2" / f, imp)
    wrapper = spec.cert_dir / f"Imported{name}.v"
    require(wrapper.read_text() == f'From LeanImport Require Import Lean.\nLean Import "{name}.out".\n',
            "import wrapper changed", tag)
    shutil.copy2(wrapper, imp)
    ilog = work / "import.log"
    ilog.write_text("")
    for m in ("ImportedSubadditivity", f"Imported{name}"):
        require(rocq(["-Q", str(IMPORTER), "LeanImport", "-I", str(IMPORTER), "-Q", str(imp),
                      "FoundationImported", f"{m}.v"], ilog, imp, append=True) == 0,
                f"Rocq import failed: {m}", tag)
    stamp(spec, "rocq_import", time.time() - t0)
    lines = sum(1 for _ in (imp / f"{name}.out").open("rb"))
    print(f"{tag}_PREPARE_PASS: {lines} export lines")


# --------------------------------------------------------------------------- check

def rocq_cert(spec: Spec, args: list[str], log: Path) -> int:
    w = spec.work
    return rocq(["-R", str(w / "source"), "prosa", "-Q", str(IMPORTER), "LeanImport", "-I", str(IMPORTER),
                 "-Q", str(w / "imported"), "FoundationImported",
                 "-Q", str(w / "certificates"), "FoundationCertificates", *args], log, w)


COMMON_CERTS = ("PropSPropFoundation", "LogicalRelation", "SubadditivityNatCorrespondence")
IMPORTED_REF = re.compile(r"\b(?:I|Imported\w+)\.(Prosa_[A-Za-z0-9_']+)")


def chain_order(spec: Spec) -> list[str]:
    return [*COMMON_CERTS, *spec["chain"], spec["audit_module"]]


def chain_base_key(spec: Spec) -> str:
    """Inputs shared by every certificate module of this run (Rocq side)."""
    w = spec.work
    rocq_bin = subprocess.check_output(["opam", "exec", "--switch=rocq93rc1", "--", "which", "rocq"], text=True).strip()
    packages = subprocess.check_output(["opam", "list", "--switch=rocq93rc1", "--installed", "--short",
                                        "--columns=package"], text=True).split()
    return digest({"format": 1, "rocq_sha256": sha(Path(rocq_bin)), "opam_packages": packages,
                   "importer_plugin_sha256": sha(IMPORTER / "lean_import.cmxs"),
                   "importer_foundation_sha256": sha(IMPORTER / "Lean.vo"),
                   "imported_vo": {p.name: sha(p) for p in sorted((w / "imported").glob("*.vo"))},
                   "source_vo": {str(p.relative_to(w / "source")): sha(p)
                                 for p in sorted((w / "source").rglob("*.vo"))},
                   "load_path": ["-R source prosa", "-Q importer LeanImport", "-I importer",
                                 "-Q imported FoundationImported", "-Q certificates FoundationCertificates"],
                   **({"coqeal_vo": {p.name: sha(p) for p in sorted((w / "coqeal/CoqEAL").glob("*.vo"))}}
                      if spec.get("coqeal") else {}),
                   **({"classic_prelude": {"load_path": "-Q compat Compat",
                                           "vo_sha256": sha(w / "compat/Rocq90Compat.vo")}}
                      if FAMILY == "classic" else {})})


def chain_key(previous_key: str, previous_vo: str | None, module: str, source: Path) -> str:
    return digest({"previous_key": previous_key, "previous_vo_sha256": previous_vo,
                   "module": module, "source_sha256": fsha(source)})


def checkpoint_valid(entry: dict | None, key: str, vo: Path, log: Path) -> bool:
    return bool(entry and entry.get("key") == key and vo.is_file() and log.is_file()
                and fsha(vo) == entry.get("vo_sha256") and fsha(log) == entry.get("log_sha256")
                and "Error" not in log.read_text(errors="replace"))


def exported_names(imported: Path) -> set[str]:
    """Rocq-side names (`A_B_c`) of every Lean name declared in the actual export files."""
    # mirrors rocq-lean-import's LeanName.clean_string: Unicode.ascii_of_ident, then the `toclean` table
    toclean = [("@", "__at__"), ("?", "__q"), ("!", "__B"), ("#", "__hash"), ("$", "__dollar"),
               ("%", "__pct"), ("&", "__amp"), ("\\", "__bs"), ("/", "__fs"), ("^", "__v"), ("(", "__o"),
               (")", "__c"), ("*", "__star"), ("+", "__plus"), (",", "__comma"), ("-", "__dash"),
               (":", "__co"), (";", "__semi"), ("<", "__lt"), ("=", "__eq"), (">", "__gt"),
               ("[", "__lbrack"), ("]", "__rbrack"), ("{", "__lbrace"), ("|", "__bar"), ("}", "__rbrace"),
               ("~", "__tilde")]

    def mangle(n: str) -> str:
        parts = []
        for comp in n.split("."):
            comp = "".join(c if c.isascii() else f"_UU{ord(c):04x}_" for c in comp)
            for c, r in toclean:
                comp = comp.replace(c, r)
            parts.append(comp)
        return ".".join(parts)
    names: set[str] = set()
    for out in sorted(imported.glob("*.out")):
        table = {0: ""}
        with out.open(encoding="utf-8", errors="replace") as stream:
            for line in stream:
                if (m := re.match(r"(\d+) #NS (\d+) (.+)$", line)):
                    parent = table[int(m.group(2))]
                    table[int(m.group(1))] = f"{parent}.{m.group(3).strip()}" if parent else m.group(3).strip()
                    names.add(mangle(table[int(m.group(1))]).replace(".", "_"))
                elif (m := re.match(r"(\d+) #NI (\d+) (\d+)", line)):
                    table[int(m.group(1))] = f"{table[int(m.group(2))]}.{m.group(3)}"
    return names


def preflight_missing(spec: Spec) -> dict[str, list[str]]:
    """Imported constants named by chain certificates or the imported type audit but absent from this
    run's export."""
    names = exported_names(spec.work / "imported")
    missing = {}
    files = {m: spec.work / f"certificates/{m}.v" for m in spec["chain"]}
    files["imported_type_audit"] = PROJECT / spec["imported_type_audit"]
    for m, path in files.items():
        if not path.is_file():  # a missing chain source is rejected by the chain loop
            continue
        refs = set(IMPORTED_REF.findall(path.read_text()))
        absent = sorted(n for n in refs if re.sub(r"_inst[0-9]+$", "", n) not in names)
        if absent:
            missing[m] = absent
    return missing


def check(spec: Spec) -> None:
    import time
    tag, work = spec.tag, spec.work
    require((work / f"imported/Imported{spec['export_name']}.vo").is_file(), "prepare not complete", tag)
    t0 = time.time()
    certs = work / "certificates"
    for m in COMMON_CERTS:
        shutil.copy2(V / f"certificates/common/{m}.v", certs)
    for f in spec.cert_dir.glob("*.v"):
        shutil.copy2(f, certs)
    missing = preflight_missing(spec)
    if missing:
        raise Rejected(f"{tag}_CHECK_FAILED: preflight: imported symbols absent from the export: "
                       + json.dumps(missing))
    checkpoint_path = certs / "chain_checkpoints.json"
    try:
        checkpoints = read(checkpoint_path) if checkpoint_path.is_file() else {}
    except json.JSONDecodeError:
        checkpoints = {}

    def save() -> None:
        tmp = checkpoint_path.with_suffix(".tmp")
        tmp.write_text(json.dumps(checkpoints, indent=2) + "\n")
        tmp.replace(checkpoint_path)

    key, vo_sha, compiled, reused = chain_base_key(spec), None, 0, 0
    for m in chain_order(spec):
        if not (certs / f"{m}.v").is_file():  # e.g. the audit module, generated at finalization
            raise Rejected(f"{tag}_CHECK_FAILED: missing certificate source {m}.v "
                           f"(compiled {compiled}, reused {reused} before it)")
        key = chain_key(key, vo_sha, m, certs / f"{m}.v")
        vo, log = certs / f"{m}.vo", certs / f"{m}.log"
        if checkpoint_valid(checkpoints.get(m), key, vo, log):
            reused += 1
        else:
            checkpoints.pop(m, None)
            save()
            if rocq_cert(spec, [f"certificates/{m}.v"], log) != 0:
                print(log.read_text()[-3000:], file=sys.stderr)
                raise Rejected(f"{tag}_CHECK_FAILED: {m}")
            checkpoints[m] = {"key": key, "vo_sha256": sha(vo), "log_sha256": fsha(log)}
            save()
            compiled += 1
        vo_sha = checkpoints[m]["vo_sha256"]
    stamp(spec, "certificate_compile", time.time() - t0, f"COMPILED={compiled};REUSED={reused}")
    print(f"{tag}_CERTIFICATES: compiled {compiled}, reused {reused}")
    t0 = time.time()
    if rocq_cert(spec, [str(PROJECT / spec["imported_type_audit"])], work / "imported_type_audit.log") != 0:
        print((work / "imported_type_audit.log").read_text()[-3000:], file=sys.stderr)
        raise Rejected(f"{tag}_CHECK_FAILED: imported type audit")
    stamp(spec, "imported_type_audit", time.time() - t0)
    t0 = time.time()
    if run([sys.executable, str(V / "scripts/audit_lean_axioms.py"), "--config", str(V / spec["lean_axiom_config"]),
            "--log", "lean_type_audit.log", "--output", "lean_axiom_summary.json"],
           work / "lean_axiom_classifier.log", work) != 0:
        print((work / "lean_axiom_classifier.log").read_text()[-3000:], file=sys.stderr)
        raise Rejected(f"{tag}_CHECK_FAILED: Lean axiom audit")
    stamp(spec, "lean_axiom_audit", time.time() - t0)
    t0 = time.time()
    if run([sys.executable, str(V / "scripts/audit_assumptions.py"), "--config", str(V / spec["assumption_config"]),
            "--log", f"certificates/{spec['audit_module']}.log", "--output", "assumption_summary.json"],
           work / "assumption_classifier.log", work) != 0:
        text = (work / "assumption_classifier.log").read_text()
        print("\n".join(l for l in text.splitlines() if "unexpected" in l or "\"" in l)[-3000:], file=sys.stderr)
        raise Rejected(f"{tag}_CHECK_FAILED: assumption audit")
    stamp(spec, "assumption_audit", time.time() - t0)
    print(f"{tag}_CHECK_PASS")


# --------------------------------------------------------------------------- publish

def fingerprint_matches(spec: Spec, rows: list[dict]) -> dict:
    evidence = type_evidence(spec)
    # opt-in (CoqEAL specs): official-toolchain evidence for the declarations the inventory marks as the CoqEAL
    # build boundary, produced by scripts/elaborate_coqeal_declaration_types.py (see its docstring)
    coqeal_evidence = (read(DEP / "coqeal_declaration_type_evidence.json")["declarations"]
                       if spec.get("coqeal") else {})
    log = (spec.work / "source_type_fingerprint.log").read_text()
    require("Error" not in log, "Rocq source type audit failed", spec.tag)
    blocks = {m.group(1): " ".join(m.group(2).split())
              for m in re.finditer(r"(?ms)^BEGIN\|([^\n]+)\n(.*?)^END\|\1\s*$", log)}
    result = {}
    for row in rows:
        name = row["qualified_name"]
        if name in coqeal_evidence:
            item = coqeal_evidence[name]
            require(row["type_evidence_status"] == "UNRESOLVED_EXTERNAL_BUILD_BOUNDARY_COQEAL"
                    and item["inventory_fingerprint"] == row["final_type_or_type_fingerprint"]
                    and item["source_file"] == spec.source,
                    f"CoqEAL type evidence not bound to the inventory row: {name}", spec.tag)
        else:
            item = evidence[name]
            require(row["final_type_or_type_fingerprint"] == "rocq-check-sha256:" + item["sha256"],
                    f"source type evidence changed for {name}", spec.tag)
        got = blocks.get(name)
        require(got is not None, f"missing source fingerprint: {name}", spec.tag)
        if hashlib.sha256(got.encode()).hexdigest() == item["sha256"]:
            result[name] = "EXACT_HASH"
            continue
        # The official `Check @name` may print the declaration qualified by its
        # own file module (`@readiness.x`) when another `x` was in scope there;
        # accept exactly that display qualifier and nothing else.
        own, short = name.split(".")[-2], name.split(".")[-1]
        # the display qualifier may also be a longer trailing suffix of the
        # file's own logical path (`@restricted_supply.busy_prefix.x` when two
        # files named `busy_prefix` declare `x`); it still names this file only
        path = name.split(".")[1:-1]
        own_qualifiers = [".".join(path[i:]) for i in range(len(path) - 1, -1, -1)]
        # classic family: a declaration name carries its Rocq module path (`ResponseTime.x`), which the validation
        # context displays (`@ResponseTime.x`); the official context may prefix it with a trailing suffix of the
        # file's own logical path (`@global.response_time.ResponseTime.x`, when another loaded file declares the same
        # `Module`).  Accept exactly those file-path qualifiers in front of exactly this declaration name.
        dname = row["declaration_name"]
        if spec.get("family", "v06") == "classic" and "." in dname and name.endswith("." + dname):
            fpath = name[: -len(dname) - 1].split(".")[1:]
            for qual in [".".join(fpath[i:]) for i in range(len(fpath) - 1, -1, -1)]:
                for prefix in ("@", ""):
                    head = f"{prefix}{qual}.{dname} : "
                    if item["normalized_check"].startswith(head) and \
                            got == f"{prefix}{dname} : " + item["normalized_check"][len(head):]:
                        result[name] = "EXACT_MODULO_OWN_MODULE_QUALIFIER"
                        break
                if name in result:
                    break
            if name in result:
                continue
        matched_qualifier = False
        for qual in own_qualifiers:
            qualified = f"@{qual}.{short} : "
            if item["normalized_check"].startswith(qualified) and \
                    got == f"@{short} : " + item["normalized_check"][len(qualified):]:
                matched_qualifier = True
                break
            # a declaration without implicit arguments is displayed by `Check @name`
            # without the `@` (`readiness.x : T`); accept the same display qualifier
            bare = f"{qual}.{short} : "
            if item["normalized_check"].startswith(bare) and \
                    got == f"{short} : " + item["normalized_check"][len(bare):]:
                matched_qualifier = True
                break
        if matched_qualifier:
            result[name] = "EXACT_MODULO_OWN_MODULE_QUALIFIER"
            continue
        # opt-in (spec `own_qualified_in_type`, a list of this file's own declaration names): the official evidence
        # context loads every module, including later files that declare the same short names (e.g. `eq_taskab` in
        # EDF/FP refinements), so the official `Check` prints those own declarations qualified by this file's own
        # module, also inside the type.  Accept exactly that qualifier on exactly the listed own names, nothing else.
        own_in_type = spec.get("own_qualified_in_type", [])
        if own_in_type:
            require(set(own_in_type) <= {r["declaration_name"] for r in rows},
                    "own_qualified_in_type lists a name that is not a declaration of this file", spec.tag)
            repaired = item["normalized_check"]
            for qual in own_qualifiers:
                for own in own_in_type:
                    repaired = re.sub(r"(?<![\w.'])" + re.escape(f"{qual}.{own}") + r"(?![\w'])", own, repaired)
            # classic family: an own name carrying its Rocq module path (`ResponseTime.x`) is qualified by trailing
            # suffixes of its file's logical path (`global.response_time.ResponseTime.x`)
            if spec.get("family", "v06") == "classic":
                for own in own_in_type:
                    if "." not in own:
                        continue
                    full = [r["qualified_name"] for r in rows if r["declaration_name"] == own]
                    require(len(full) == 1, f"own_qualified_in_type: ambiguous own name {own}", spec.tag)
                    fpath = full[0][: -len(own) - 1].split(".")[1:]
                    for qual in [".".join(fpath[i:]) for i in range(len(fpath) - 1, -1, -1)]:
                        repaired = re.sub(r"(?<![\w.'])" + re.escape(f"{qual}.{own}") + r"(?![\w'])", own, repaired)
                # together with the file-path display qualifier of this declaration's own head (as accepted above)
                if "." in dname and name.endswith("." + dname):
                    fpath = name[: -len(dname) - 1].split(".")[1:]
                    for qual in [".".join(fpath[i:]) for i in range(len(fpath) - 1, -1, -1)]:
                        for prefix in ("@", ""):
                            if repaired.startswith(f"{prefix}{qual}.{dname} : "):
                                repaired = prefix + repaired[len(prefix + qual + "."):]
            if repaired != item["normalized_check"] and got == repaired:
                result[name] = "EXACT_MODULO_OWN_MODULE_QUALIFIER"
                continue
        # opt-in (spec `dependency_qualified_in_type`, a list of fully qualified declarations of files of the official
        # closure): the official evidence context also loads later files that declare the same short names (e.g.
        # `Task` in job_constructor and EDF/FP), so the official `Check` prints such a dependency declaration
        # qualified by a trailing suffix of its own module path (`task.Task`).  Accept exactly those qualifiers on
        # exactly the listed declarations, and only when no other declaration of the closure has the same short name
        # (so the unqualified name of the validation context denotes that declaration); nothing else.
        dep_in_type = spec.get("dependency_qualified_in_type", [])
        # classic family: a closure dependency's name carries its Rocq module path (`Platform.work_conserving`), which
        # the validation context displays; the official context prefixes it with a trailing suffix of its file's
        # logical path (`global.basic.platform.Platform.work_conserving`) when another loaded file declares the same
        # `Module` (e.g. `apa/platform.v`).  Accept exactly those qualifiers on exactly the listed closure declarations
        # (whose module-path name must be unique among the closure's declarations), together with exactly the own
        # qualifiers accepted above (the head, and the `own_qualified_in_type` names inside the type); nothing else.
        if dep_in_type and spec.get("family", "v06") == "classic":
            closure = set(official_closure_files(spec)[0])
            with (DEP / "declaration_inventory.csv").open() as stream:
                closure_rows = [r for r in csv.DictReader(stream) if r["source_file"] in closure]
            repaired = item["normalized_check"]
            for full in dep_in_type:
                hits = [r for r in closure_rows if r["qualified_name"] == full]
                require(len(hits) == 1 and hits[0]["source_file"] != spec.source,
                        f"dependency_qualified_in_type: not a closure dependency declaration: {full}", spec.tag)
                dname_dep = hits[0]["declaration_name"]
                require([r["qualified_name"] for r in closure_rows if r["declaration_name"] == dname_dep] == [full],
                        f"dependency_qualified_in_type: module-path name not unique in the closure: {full}", spec.tag)
                fpath = full[: -len(dname_dep) - 1].split(".")[1:]
                for qual in [".".join(fpath[i:]) for i in range(len(fpath) - 1, -1, -1)]:
                    repaired = re.sub(r"(?<![\w.'])" + re.escape(f"{qual}.{dname_dep}") + r"(?![\w'])", dname_dep,
                                      repaired)
            for own in own_in_type:
                if "." not in own:
                    continue
                full_own = [r["qualified_name"] for r in rows if r["declaration_name"] == own]
                require(len(full_own) == 1, f"own_qualified_in_type: ambiguous own name {own}", spec.tag)
                fpath = full_own[0][: -len(own) - 1].split(".")[1:]
                for qual in [".".join(fpath[i:]) for i in range(len(fpath) - 1, -1, -1)]:
                    repaired = re.sub(r"(?<![\w.'])" + re.escape(f"{qual}.{own}") + r"(?![\w'])", own, repaired)
            if "." in dname and name.endswith("." + dname):
                fpath = name[: -len(dname) - 1].split(".")[1:]
                for qual in [".".join(fpath[i:]) for i in range(len(fpath) - 1, -1, -1)]:
                    for prefix in ("@", ""):
                        if repaired.startswith(f"{prefix}{qual}.{dname} : "):
                            repaired = prefix + repaired[len(prefix + qual + "."):]
            if repaired != item["normalized_check"] and got == repaired:
                result[name] = "EXACT_MODULO_DEPENDENCY_AND_OWN_MODULE_QUALIFIER"
                continue
        if dep_in_type and spec.get("family", "v06") != "classic":
            closure = set(official_closure_files(spec)[0])
            with (DEP / "declaration_inventory.csv").open() as stream:
                closure_rows = list(csv.DictReader(stream))
            repaired = item["normalized_check"]
            for full in dep_in_type:
                src_of = [r["source_file"] for r in closure_rows if r["qualified_name"] == full]
                require(len(src_of) == 1 and src_of[0] in closure and src_of[0] != spec.source,
                        f"dependency_qualified_in_type: not a closure dependency declaration: {full}", spec.tag)
                dshort = full.split(".")[-1]
                require([r["qualified_name"] for r in closure_rows
                         if r["declaration_name"] == dshort and r["source_file"] in closure] == [full],
                        f"dependency_qualified_in_type: short name not unique in the closure: {full}", spec.tag)
                dpath = full.split(".")[1:-1]
                for qual in [".".join(dpath[i:]) for i in range(len(dpath) - 1, -1, -1)]:
                    repaired = re.sub(r"(?<![\w.'])" + re.escape(f"{qual}.{dshort}") + r"(?![\w'])", dshort,
                                      repaired)
            if repaired != item["normalized_check"] and got == repaired:
                result[name] = "EXACT_MODULO_DEPENDENCY_MODULE_QUALIFIER"
                continue
            # together with exactly the accepted Rocq 9.0/9.3 display difference of a final parenthesised
            # `exists` operand of `\/`, `<->` or `~` (the `TYPE_EQUAL_MODULO_EXISTS_PARENS` normalization below)
            repaired_unparen = re.sub(r"(\\/|<->|~) \((exists .*)\)$", r"\1 \2", repaired)
            if repaired != item["normalized_check"] and repaired_unparen != repaired and got == repaired_unparen:
                result[name] = "EXACT_MODULO_DEPENDENCY_MODULE_QUALIFIER_AND_EXISTS_PARENS"
                continue
            # together with exactly the own-module qualifiers accepted above: the display qualifier at the head
            # (`@qual.x : `/`qual.x : `) and, for the names listed in `own_qualified_in_type`, inside the type
            if repaired != item["normalized_check"]:
                both = repaired
                for qual in own_qualifiers:
                    for own in own_in_type:
                        both = re.sub(r"(?<![\w.'])" + re.escape(f"{qual}.{own}") + r"(?![\w'])", own, both)
                heads = [both] + [prefix + both[len(prefix + qual + "."):]
                                  for qual in own_qualifiers for prefix in ("@", "")
                                  if both.startswith(f"{prefix}{qual}.{short} : ")]
                if got in heads and got != repaired:
                    result[name] = "EXACT_MODULO_DEPENDENCY_AND_OWN_MODULE_QUALIFIER"
                    continue
        # MathComp 2.4 (official evidence) displays the carrier of the canonical
        # integer structure that types `(x - y)%R` as
        # `ssrint_int__canonical__GRing_Nmodule`; MathComp 2.6 (the validation
        # toolchain) displays the same carrier as
        # `ssrint_int__canonical__Algebra_BaseAddMagma` (both have `sort := int`).
        # Accept exactly that display difference in a declaration type (optionally
        # with the own-module display qualifier), nothing else.
        mc_int = re.sub(r"(?<![\w.'])ssrint_int__canonical__GRing_Nmodule(?![\w'])",
                        "ssrint_int__canonical__Algebra_BaseAddMagma", item["normalized_check"])
        if mc_int != item["normalized_check"] and any(
                mc_int.startswith(q) and got == f"@{short} : " + mc_int[len(q):]
                for q in [f"@{short} : "] + [f"@{qual}.{short} : " for qual in own_qualifiers]):
            result[name] = "TYPE_EQUAL_MODULO_MATHCOMP_INT_CARRIER_DISPLAY"
            continue
        # the accepted Rocq 9.0/9.3 display difference of a final parenthesised `exists` operand of `\/`, `<->`
        # or `~` (`TYPE_EQUAL_MODULO_EXISTS_PARENS`, below for extracted statement bodies), on the `Check @name`
        # output of an official-closure source: exactly that removal, nothing else
        # the accepted Rocq 9.0/9.3 display difference of a parenthesised `fun=>` body lambda
        # (`TYPE_EQUAL_MODULO_SSR_FUN_WILDCARD_BODY_PARENS`, below for extracted statement bodies), on the
        # `Check @name` output of an official-closure source (optionally with the own-module display qualifier):
        # exactly that removal, nothing else
        ssr_check = ssr_fun_body_unparen(item["normalized_check"])
        if ssr_check != item["normalized_check"] and (got == ssr_check or any(
                ssr_check.startswith(q) and got == f"@{short} : " + ssr_check[len(q):]
                for q in [f"@{short} : "] + [f"@{qual}.{short} : " for qual in own_qualifiers])):
            result[name] = "TYPE_EQUAL_MODULO_SSR_FUN_WILDCARD_BODY_PARENS"
            continue
        unparen_check = re.sub(r"(\\/|<->|~) \((exists .*)\)$", r"\1 \2", item["normalized_check"])
        if unparen_check != item["normalized_check"] and got == unparen_check:
            result[name] = "TYPE_EQUAL_MODULO_EXISTS_PARENS"
            continue
        m = re.match(r"statement_\S+ = (.*) : (Prop|Type)$", got)
        ref = item["normalized_check"].split(" : ", 1)[1]
        body = m.group(1) if m else None
        unparen = re.sub(r"(\\/|<->|~) \((exists .*)\)$", r"\1 \2", ref)
        # MathComp 2.4 (official evidence) prints `@Order.max`/`@Order.min`
        # through the abbreviations `Order.Def.max := @Order.max` and
        # `Order.Def.min := @Order.min`; MathComp 2.6 (the validation toolchain)
        # prints the same constants unabbreviated.  Accept exactly that display
        # difference, nothing else.
        mc_order = re.sub(r"(?<![\w.'])Order\.Def\.(max|min)(?![\w'])", r"Order.\1", ref)
        # A statement may name a declaration of this same file qualified by the
        # file's own module (`edf.x`, or a longer trailing suffix of the file's
        # own logical path such as `edf.fully_preemptive.x`, as in the `Check`
        # rule above) when another `x` was in scope in the official environment;
        # the extraction repairs exactly that qualifier to the local name
        # (recorded printer repair `qual.x=x` for a declaration `x` of this
        # file, including a source-local helper block of this file such as a
        # `#[local] Instance` named by the statements).  Accept exactly those
        # recorded repairs, nothing else.
        # MathComp 2.4 (official evidence) prints a big operator that is the right
        # operand of `*` at the end of a type with parentheses (`k * (\\sum_(i <- r) F i)`);
        # MathComp 2.6 (the validation toolchain) prints the same term without them
        # (`k * \\sum_(i <- r) F i`).  Accept exactly the removal of such a final
        # parenthesised `\\sum_` operand, nothing else.
        mc_sum = ref
        opener = mc_sum.rfind(" * (\\sum_")
        if opener >= 0:
            start, depth, close = opener + 3, 0, None
            for k in range(start, len(mc_sum)):
                depth += {"(": 1, ")": -1}.get(mc_sum[k], 0)
                if depth == 0:
                    close = k
                    break
            if close == len(mc_sum) - 1:
                mc_sum = mc_sum[:start] + mc_sum[start + 1:close]
        # Rocq 9.0 (official evidence) prints a lambda that is the body of
        # ssreflect's `fun=>` (`fun _ => ...`) with parentheses
        # (`fun=> (fun R : T => e)`); Rocq 9.3 (the validation toolchain) prints
        # the same term without them (`fun=> fun R : T => e`).  Accept exactly the
        # removal of the parentheses around such a `fun=>` body lambda, nothing else.
        ssr_fun = ssr_fun_body_unparen(ref)
        # declarations of this same file: its inventory declarations and its
        # source-local helper blocks (extracted byte-identically from this file)
        own_names = {r["declaration_name"] for r in inventory(spec)} | \
            set((spec.get("extraction") or {}).get("helper_blocks", []))
        own_repairs = [tuple(r.split("=", 1)) for r in
                       (spec.get("extraction") or {}).get("printer_repairs", [])]
        own_repairs = [(old, new) for old, new in own_repairs
                       if new in own_names and any(old == f"{qual}.{new}" for qual in own_qualifiers)]
        repaired = ref
        for old, new in own_repairs:
            repaired = re.sub(rf"(?<![\w.']){re.escape(old)}(?![\w'])", new, repaired)
        # both accepted display differences at once: the MathComp `Order.Def`
        # abbreviation and a recorded own-module qualifier repair (each exactly as
        # accepted above), nothing else
        mc_order_repaired = mc_order
        for old, new in own_repairs:
            mc_order_repaired = re.sub(rf"(?<![\w.']){re.escape(old)}(?![\w'])", new, mc_order_repaired)
        result[name] = ("STATEMENT_BODY_EQUAL_TO_ELABORATED_TYPE" if body == ref
                        else "TYPE_EQUAL_MODULO_EXISTS_PARENS" if body is not None and body == unparen
                        and unparen != ref
                        else "TYPE_EQUAL_MODULO_MATHCOMP_ORDER_DEF_ABBREVIATION"
                        if body is not None and body == mc_order and mc_order != ref
                        else "TYPE_EQUAL_MODULO_MATHCOMP_BIGOP_OPERAND_PARENS"
                        if body is not None and body == mc_sum and mc_sum != ref
                        else "TYPE_EQUAL_MODULO_SSR_FUN_WILDCARD_BODY_PARENS"
                        if body is not None and body == ssr_fun and ssr_fun != ref
                        else "STATEMENT_BODY_EQUAL_MODULO_OWN_MODULE_QUALIFIER"
                        if own_repairs and body is not None and body == repaired and repaired != ref
                        else "TYPE_EQUAL_MODULO_MATHCOMP_ORDER_DEF_ABBREVIATION_AND_OWN_MODULE_QUALIFIER"
                        if own_repairs and body is not None and body == mc_order_repaired
                        and mc_order != ref and mc_order_repaired != mc_order
                        else "MISMATCH")
        require(result[name] != "MISMATCH", f"source type mismatch: {name}: {got}", spec.tag)
    return result


def publish(spec: Spec) -> None:
    tag, work = spec.tag, spec.work
    official = SOURCE_ROOT / spec.source
    require(git(SOURCE_ROOT, "rev-parse", "HEAD") == PIN, "source commit changed", tag)
    require(git(SOURCE_ROOT, "rev-parse", "HEAD^{tree}") == TREE, "source tree changed", tag)
    require(not git(SOURCE_ROOT, "status", "--porcelain", "--untracked-files=all"), "pinned source dirty", tag)
    with (DEP / "file_inventory.csv").open() as stream:
        row = next(r for r in csv.DictReader(stream) if r["file"] == spec.source)
    require(row["sha256"] == sha(official), "file inventory mismatch", tag)
    dag = read(DEP / "file_dag.json")
    deps = {e["dependency_file"] for e in dag["edges"] if e["dependent_file"] == spec.source}
    require(deps == set(spec["dependencies"]), f"file DAG changed: {sorted(deps)}", tag)
    dependency_evidence = {d: accepted_status(d) for d in sorted(deps)}
    rows = inventory(spec)
    targets = [r["declaration_name"] for r in rows]
    require(len(targets) == spec["declaration_count"], "declaration inventory changed", tag)
    computational = set(spec.get("computational", []))

    # source binding
    mode = spec["source_mode"]
    copied = work / "source" / spec.source
    compat: dict = {"mode": mode}
    if FAMILY == "classic":
        compat["classic_prelude"] = {
            "file": str(CLASSIC["prelude_source"].relative_to(PROJECT)), "sha256": CLASSIC["prelude_sha256"],
            "vo_sha256": sha(work / "compat/Rocq90Compat.vo"),
            "flags": "-Q compat Compat -ri Compat.Rocq90Compat (classic/ source files only)"}
    if mode == "pinned":
        require(sha(copied) == sha(official), "compiled source copy is not byte-identical", tag)
        source_vo = copied.with_suffix(".vo")
        compat["note"] = "pinned source compiled byte-identically"
    elif mode == "official_closure":
        closure, patched = official_closure_files(spec)
        with tempfile.TemporaryDirectory() as tmp:
            for rel in closure:
                (Path(tmp) / rel).parent.mkdir(parents=True, exist_ok=True)
                shutil.copy2(SOURCE_ROOT / rel, Path(tmp) / rel)
            for patch in spec["official_closure"]["patches"]:
                subprocess.run(["patch", "-s", "-p1", "-i", str(V / patch)], cwd=tmp, check=True)
            for rel in closure:
                require(sha(work / "source" / rel) == sha(Path(tmp) / rel),
                        f"closure file is not official + recorded patches: {rel}", tag)
        if spec.source in patched and spec["official_closure"].get("module_change") == "proof_only_patch":
            require(module_proof_only(official, copied), "module change is not confined to proof scripts", tag)
            compat["module_change"] = ("recorded proof-only patch (lines inside Proof ... Qed only; no Admitted/admit/"
                                       "axiom; user decision 2026-10-03)")
        elif spec.source in patched:
            require(module_flag_only(official, copied), "module change is not exactly the rewrite-order flag", tag)
            compat["module_change"] = "one added line `" + REWRITE_ORDER_FLAG + "` (file-local rewrite-order flag)"
        else:
            require(sha(copied) == sha(official), "compiled module is not byte-identical", tag)
        source_vo = copied.with_suffix(".vo")
        compat.update(note="official proof closure (pinned files + recorded compatibility patches); module "
                           "compiled byte-identically" + ((" except the recorded proof-only patch"
                                                          if spec["official_closure"].get("module_change") ==
                                                          "proof_only_patch" else
                                                          " except the recorded rewrite-order flag")
                                                         if spec.source in patched else ""),
                      closure_files=closure, closure_list_sha256=sha(V / spec["official_closure"]["files"]),
                      patches={p: sha(V / p) for p in spec["official_closure"]["patches"]},
                      patched_files=sorted(patched))
    elif mode == "patched":
        with tempfile.TemporaryDirectory() as tmp:
            probe = Path(tmp) / spec.source
            probe.parent.mkdir(parents=True)
            shutil.copy2(official, probe)
            for patch in spec["patches"]:
                subprocess.run(["patch", "-s", "-p1", "-i", str(V / patch)], cwd=tmp, check=True)
            require(sha(copied) == sha(probe), "compiled source is not official + audited patches", tag)
        for patch in spec["patches"]:
            removed = [l for l in (V / patch).read_text().splitlines()
                       if l.startswith("-") and not l.startswith("---")]
            require(removed == spec["patch_removed_lines"][patch], f"patch scope changed: {patch}", tag)
        source_vo = copied.with_suffix(".vo")
        compat.update(note="pinned source + audited proof-only patches",
                      patches={p: sha(V / p) for p in spec["patches"]})
    else:
        x = spec["extraction"]
        meta = read(work / "source_extraction.json")
        extracted = work / "source" / f"{x['module']}.v"
        require(meta["source_file_sha256"] == sha(official) and meta["source_commit"] == PIN
                and meta["mode"] == "proof_independent_semantic_source_signature",
                "extraction not bound to pinned source", tag)
        require(meta["transformations"]["dropped_irrelevant_imports"] == sorted(x.get("drop_imports", []))
                and meta["transformations"]["added_validation_imports"] == x.get("add_imports", []),
                "unexpected dropped/added imports", tag)
        require(not ESCAPE_ROCQ.search(extracted.read_text()), "extracted source escape", tag)
        helper_blocks = set(x.get("helper_blocks", []))
        require(set(meta["declarations"]) == set(targets) | helper_blocks, "extraction declaration set changed", tag)
        # a body may differ from the pinned block only by parentheses that make the
        # validation toolchain reproduce the authoritative (official-toolchain) parse;
        # the extractor checks that only parentheses were added, and the spec must
        # carry the official-toolchain print of the body as evidence
        parens = {i["name"]: i for i in x.get("body_parenthesizations", [])}
        require(meta["transformations"].get("body_parenthesizations", {})
                == {n: {"old": i["old"], "new": i["new"]} for n, i in parens.items()},
                "unexpected body parenthesizations", tag)
        for i in parens.values():
            require((PROJECT / i["evidence"]).is_file(), f"missing parse evidence: {i['name']}", tag)
        for name, item in meta["declarations"].items():
            if name in parens:
                require(item["acquisition_mode"] == "BODY_PARENTHESIZED",
                        f"parenthesized body mode changed: {name}", tag)
            elif name in computational or name in helper_blocks:
                require(item["acquisition_mode"] == "BODY_EXACT"
                        and item["generated_text_sha256"] == item["source_block_sha256"],
                        f"computational body not byte-identical: {name}", tag)
            else:
                require(item["acquisition_mode"] == "STATEMENT_EXACT_PROOF_OMITTED",
                        f"statement extraction mode changed: {name}", tag)
        source_vo = extracted.with_suffix(".vo")
        if parens:
            compat["body_parenthesizations"] = {
                n: {"old": i["old"], "new": i["new"], "evidence": i["evidence"],
                    "evidence_sha256": sha(PROJECT / i["evidence"])} for n, i in parens.items()}
        compat.update(note=x.get("note", "proof-independent semantic extraction"),
                      extracted_sha256=sha(extracted),
                      extraction_metadata_sha256=sha(work / "source_extraction.json"))
    require(sha(source_vo) and "Error" not in (work / "source_build.log").read_text(), "source .vo", tag)
    if spec.get("extra_source_patches"):
        with tempfile.TemporaryDirectory() as tmp:
            for rel in spec["extra_pinned_sources"]:
                (Path(tmp) / rel).parent.mkdir(parents=True, exist_ok=True)
                shutil.copy2(SOURCE_ROOT / rel, Path(tmp) / rel)
            for patch in spec["extra_source_patches"]:
                subprocess.run(["patch", "-s", "-p1", "-i", str(V / patch)], cwd=tmp, check=True)
            for rel in spec["extra_pinned_sources"]:
                require(sha(work / "source" / rel) == sha(Path(tmp) / rel), f"extra source changed: {rel}", tag)
    else:
        for rel in spec.get("extra_pinned_sources", []):
            require(sha(work / "source" / rel) == sha(SOURCE_ROOT / rel), f"extra source changed: {rel}", tag)
    for rel, (stem, key) in spec.get("extra_source_vo_checks", {}).items():
        require(sha(work / "source" / rel) == manifest_hash(stem, key), f"extra source .vo changed: {rel}", tag)
    for art in spec.get("extra_artifacts", []):
        require(sha(work / art["to"]) == manifest_hash(art["manifest"], art["key"]), f"artifact changed: {art['to']}", tag)
    for art in spec.get("extra_olean_artifacts", []):
        require(sha(work / "olean" / art["to"]) == extra_olean_hash(art),
                f"olean artifact changed: {art['to']}", tag)
    for lean_src, out, stem, *key in spec.get("extra_lean", []):
        if stem:
            require(sha(work / "olean" / out) == manifest_hash(stem, key[0] if key else "production_olean_sha256"),
                    f"dependency olean changed: {out}", tag)
    for check in spec["base_checks"]:
        if check.get("olean"):
            require(sha(work / "olean" / check["olean"]) ==
                    manifest_hash(check["manifest"], check.get("olean_key", "production_olean_sha256")),
                    f"dependency olean changed: {check['olean']}", tag)
        if check.get("vo"):
            require(sha(work / "source" / check["vo"]) ==
                    manifest_hash(check["manifest"], check.get("vo_key", "source_vo_sha256")),
                    f"dependency vo changed: {check['vo']}", tag)
    if spec.get("coqeal"):
        compat["coqeal"] = coqeal_record(spec)
    matches = fingerprint_matches(spec, rows)

    # toolchain
    out = lambda *a: subprocess.check_output(a, text=True, cwd=PROJECT).strip()
    require("Lean (version 4.33.1" in out("lake", "env", "lean", "--version")
            and git(PROJECT / ".lake/packages/mathlib", "rev-parse", "HEAD")
            == "0df444a360eaa60ab8c11dca51a86af692955474"
            and "9.3" in out("opam", "exec", "--switch=rocq93rc1", "--", "rocq", "--version"),
            "toolchain changed", tag)
    tooling = read(V / "tooling/tooling_manifest.json")
    require(sha(V / ".work/tooling/lean4export/.lake/build/bin/lean4export")
            == tooling["lean4export"]["expected_binary_sha256"]
            and sha(IMPORTER / "lean_import.cmxs") == tooling["rocq_lean_import"]["expected_plugin_sha256"]
            and sha(IMPORTER / "Lean.vo") == tooling["rocq_lean_import"]["expected_foundation_vo_sha256"],
            "export/import tooling changed", tag)

    # Lean
    production = PROJECT / spec["production"]
    target_olean = work / "olean" / spec["production_olean"]
    require(target_olean.stat().st_mtime_ns > production.stat().st_mtime_ns, "target .olean stale", tag)
    require(not ESCAPE_LEAN.search(production.read_text()), "forbidden Lean escape", tag)
    ns = spec["lean_namespace"] + "."
    lean_log = (work / "lean_type_audit.log").read_text()
    require("error" not in lean_log.lower() and "sorryAx" not in lean_log
            and all(ns + n in lean_log for n in targets), "Lean type audit failed", tag)
    lean_axioms = read(work / "lean_axiom_summary.json")
    require(not lean_axioms["missing"] and not lean_axioms["extra"]
            and set(lean_axioms["declarations"]) >= {ns + n for n in targets}
            and all(i["status"] == "PASS" and not i["unexpected_axioms"]
                    for i in lean_axioms["declarations"].values()), "Lean axiom audit failed", tag)

    # export / import
    name = spec["export_name"]
    export_config = V / spec["export_config"].removeprefix("Validation/")
    exported = work / f"imported/{name}.out"
    imported_vo = work / f"imported/Imported{name}.vo"
    metadata = read(work / "export_metadata.json")
    config = read(export_config)
    # opt-in (classic configs): auxiliary theorems exported statement-only as well (e.g. `_proof_N` of an informative
    # definition); they are part of the recorded statement-only export boundary
    statement_only = [ns + n for n in targets if n not in computational] + list(spec.get("extra_statement_only", []))
    require(config["statement_only"] == statement_only
            and metadata["statement_only_count"] == len(statement_only)
            and all(ns + n in config["targets"] for n in targets)
            and all(ns + n in config["definition_targets"] for n in computational)
            and metadata["config_sha256"] == sha(export_config)
            and metadata["output_sha256"] == sha(exported),
            "export metadata/configuration changed", tag)
    require(imported_vo.stat().st_mtime_ns > exported.stat().st_mtime_ns, "imported .vo stale", tag)
    require(sha(work / "imported/Subadditivity.out") == sha(V / "imported/foundation_slice_2/Subadditivity.out"),
            "shared Nat artifact changed", tag)
    type_audit = (work / "imported_type_audit.log").read_text()
    prefix = spec["lean_namespace"].replace(".", "_") + "_"
    # the Rocq importer spells non-ASCII identifier characters as `_UU<hex4>_`
    # mirrors rocq-lean-import's LeanName.clean_string: Unicode.ascii_of_ident, then the `toclean` table
    toclean = [("@", "__at__"), ("?", "__q"), ("!", "__B"), ("#", "__hash"), ("$", "__dollar"),
               ("%", "__pct"), ("&", "__amp"), ("\\", "__bs"), ("/", "__fs"), ("^", "__v"), ("(", "__o"),
               (")", "__c"), ("*", "__star"), ("+", "__plus"), (",", "__comma"), ("-", "__dash"),
               (":", "__co"), (";", "__semi"), ("<", "__lt"), ("=", "__eq"), (">", "__gt"),
               ("[", "__lbrack"), ("]", "__rbrack"), ("{", "__lbrace"), ("|", "__bar"), ("}", "__rbrace"),
               ("~", "__tilde")]

    def mangle(n: str) -> str:
        parts = []
        for comp in n.split("."):
            comp = "".join(c if c.isascii() else f"_UU{ord(c):04x}_" for c in comp)
            for c, r in toclean:
                comp = comp.replace(c, r)
            parts.append(comp)
        return ".".join(parts)
    require("Error" not in type_audit and all(prefix + mangle(n).replace(".", "_") in type_audit for n in targets),
            "imported type audit failed", tag)

    # certificates
    modules = spec["chain"] + [spec["audit_module"]]
    for m in modules:
        require(sha(spec.cert_dir / f"{m}.v") == sha(work / f"certificates/{m}.v"), f"certificate differs: {m}", tag)
        require(sha(work / f"certificates/{m}.vo")
                and "Error" not in (work / f"certificates/{m}.log").read_text(), f"cert compile: {m}", tag)
        require(not ESCAPE_ROCQ.search((spec.cert_dir / f"{m}.v").read_text()), f"certificate escape: {m}", tag)
    for m in COMMON_CERTS:
        require(sha(V / f"certificates/common/{m}.v") == sha(work / f"certificates/{m}.v"), f"common {m}", tag)
    # every published .vo must be the checkpointed compile of the current chain inputs
    checkpoint_path = work / "certificates/chain_checkpoints.json"
    checkpoints = read(checkpoint_path)
    key, vo_sha = chain_base_key(spec), None
    for m in chain_order(spec):
        key = chain_key(key, vo_sha, m, work / f"certificates/{m}.v")
        require(checkpoint_valid(checkpoints.get(m), key, work / f"certificates/{m}.vo",
                                 work / f"certificates/{m}.log"), f"certificate checkpoint mismatch: {m}", tag)
        vo_sha = checkpoints[m]["vo_sha256"]
    provenance = work / "lean_fixture_provenance.json"
    summary = read(work / "assumption_summary.json")
    aconf = read(V / spec["assumption_config"])
    principal = spec["principal"]
    # Rocq functional extensionality: opt-in for exactly the two files of the user decision 2026-10-03
    funext_names = set(aconf.get("rocq_functional_extensionality", []))
    funext_statuses: set[str] = set()
    if funext_names:
        require(FAMILY == "classic" and spec.get("rocq_funext_scope") is True and spec.source in FUNEXT_FILES
                and funext_names <= {"FunctionalExtensionality.functional_extensionality_dep"},
                "functional extensionality outside its approved scope", tag)
        funext_statuses = {"CERTIFIED_WITH_FUNCTIONAL_EXTENSIONALITY",
                           "CERTIFIED_WITH_PROP_SPROP_FOUNDATION_AND_FUNCTIONAL_EXTENSIONALITY"}
    expected = {c for n in targets for c in principal.get(n, [cert_name(n)])} | set(spec["helpers"])
    require(summary["audit_policy"] == "fail_closed"
            and set(summary["certificates"]) == set(aconf["certificates"]) == expected
            and aconf["statement_only_dependencies"] == [], "assumption summary incomplete", tag)
    for item in summary["certificates"].values():
        require(item["status"] in {"CERTIFIED", "CERTIFIED_WITH_PROP_SPROP_FOUNDATION"} | funext_statuses
                and not item["semantic_premises"] and not item["statement_only_dependencies"]
                and not item["unexpected"] and not item["source_theorem_dependency"]
                and not item["target_theorem_dependency"], "Rocq semantic gate failed", tag)

    # baseline
    if spec["previous_status"] is None:   # the first file of the classic chain
        require(FAMILY == "classic" and spec["previous_files"] == 0 and spec["previous_decls"] == 0
                and not list(PIPE.glob("*_module_status.json")), "previous status required", tag)
        previous_path = None
        previous = {"coverage": {"translated_but_not_certified": 0, "deferred_external_boundary": 0}}
    else:
        previous_path = PIPE / spec["previous_status"]
        previous = read(previous_path)
        require(previous["status"] == "PASS"
                and previous["coverage"]["accepted_files"] == spec["previous_files"]
                and previous["coverage"]["accepted_declarations"] == spec["previous_decls"],
                "formal baseline changed", tag)
    # Prosa-fei must be unchanged while it exists; once the directory has been removed from the working tree (by
    # the user, 2026-10-01: "treat as if there is no such folder") there is nothing to compare against.
    if (ROOT / "Prosa-fei").exists():
        require(not git(ROOT, "status", "--porcelain", "--", "Prosa-fei"), "Prosa-fei changed", tag)

    now = datetime.now(timezone.utc).astimezone()
    declarations = []
    for r in rows:
        n = r["declaration_name"]
        certs = principal.get(n, [cert_name(n)])
        statuses = {summary["certificates"][c]["status"] for c in certs}
        declarations.append({
            "source_declaration": r["qualified_name"], "lean_declaration": ns + n,
            "semantic_status": (sorted(statuses & funext_statuses)[0] if statuses & funext_statuses else
                                "CERTIFIED_WITH_PROP_SPROP_FOUNDATION"
                                if "CERTIFIED_WITH_PROP_SPROP_FOUNDATION" in statuses else "CERTIFIED"),
            "certificates": certs, "semantic_premises": [],
            "source_theorem_dependency": False, "target_theorem_dependency": False,
            "acceptance": ACCEPT_DECL})
    timing = [l.split("\t") for l in (work / "stage_timing.tsv").read_text().splitlines()]
    export_lines = sum(1 for _ in exported.open("rb"))
    manifest = {
        "slice": SLICE_PREFIX + spec.slug.upper(),
        "generated_at": now.isoformat(), "published_at": now.isoformat(),
        "rank": spec["rank"], "layer": spec["layer"], "source_file": spec.source,
        "source_commit": PIN, "source_tree": TREE, "source_file_sha256": sha(official),
        "pipeline": "Validation/scripts/translation_file_pipeline.py",
        "spec": str(spec.path.relative_to(PROJECT)), "spec_sha256": sha(spec.path),
        "source_compatibility": compat, "source_type_evidence": matches,
        **({"classic_scope": {"scope": "full", "planning": str(DEP.relative_to(PROJECT)),
                              "type_evidence_sha256": sha(DEP / "declaration_type_evidence.json"),
                              "declaration_inventory_sha256": sha(DEP / "declaration_inventory.csv")}}
           if spec.get("classic_scope") == "full" else {}),
        "statement_only_export_boundary": statement_only,
        **{k: spec[k] for k in ("input_relations", "coverage_for_inner_binders",
                                "lean_representation_note") if spec.get(k) is not None},
        "export_size": {"lines": export_lines,
                        "soft_budget_flag": "OVER_100K_DIAGNOSED" if export_lines > 100000
                        else "OVER_50K_FLAGGED" if export_lines > 50000 else "WITHIN_50K",
                        **({"diagnosis": spec["export_diagnosis"]} if export_lines > 50000 else {})},
        "file_dependencies": dependency_evidence,
        "production_file": spec["production"], "production_source_sha256": sha(production),
        "production_olean_sha256": sha(target_olean),
        "export_config_sha256": sha(export_config), "export_sha256": sha(exported),
        "export_lines": export_lines, "export_bytes": exported.stat().st_size,
        "import_sha256": sha(imported_vo), "source_vo_sha256": sha(source_vo),
        "lean_axiom_summary_sha256": sha(work / "lean_axiom_summary.json"),
        "rocq_assumption_summary_sha256": sha(work / "assumption_summary.json"),
        "assumption_config_sha256": sha(V / spec["assumption_config"]),
        "stage_timing_seconds": {s: {"mode": m, "seconds": int(t)} for s, m, t in timing},
        "certificates": {m: {"source_sha256": sha(spec.cert_dir / f"{m}.v"),
                             "vo_sha256": sha(work / f"certificates/{m}.vo")} for m in modules},
        "certificate_checkpoints_sha256": sha(checkpoint_path),
        **({"lean_fixture_provenance_sha256": sha(provenance)} if provenance.is_file() else {}),
        "declarations": declarations, "acceptance": ACCEPT_FILE,
    }
    amendment = spec.get("amendment")
    n = len(targets)
    if amendment:
        # opt-in (user decision 2026-10-04): an amendment of an accepted file whose production file was changed.  The
        # accepted manifest/status (and the status chain built on them) are left untouched; the amendment re-runs every
        # stage above and is published next to them.  It must name the records it supersedes by hash and keep every
        # declaration they certified.
        aid = amendment["id"]
        require(re.fullmatch(r"amendment[0-9]+", aid) is not None, "amendment id", tag)
        old_manifest = PIPE / f"{spec.slug}_module_manifest.json"
        old_status = PIPE / f"{spec.slug}_module_status.json"
        require(sha(old_manifest) == amendment["supersedes_manifest_sha256"]
                and sha(old_status) == amendment["supersedes_status_sha256"],
                "superseded publication changed", tag)
        kept = {d["source_declaration"] for d in read(old_manifest)["declarations"]}
        require(kept <= {d["source_declaration"] for d in declarations}, "amendment drops a certified declaration", tag)
        local = set(spec.get("local_declarations", []))
        manifest["amendment"] = {
            "id": aid, "reason": amendment["reason"], "user_decision": amendment["user_decision"],
            "supersedes_manifest": old_manifest.name, "supersedes_manifest_sha256": sha(old_manifest),
            "supersedes_status": old_status.name, "supersedes_status_sha256": sha(old_status),
            "added_declarations": sorted({d["source_declaration"] for d in declarations} - kept),
            "local_declarations": sorted(r["qualified_name"] for r in rows if r["declaration_name"] in local)}
        manifest_path = PIPE / f"{spec.slug}_module_{aid}_manifest.json"
        status_path = PIPE / f"{spec.slug}_module_{aid}_status.json"
        destination = PUBLISH_DIR / f"{spec.slug}__{aid}"
    else:
        manifest_path = PIPE / f"{spec.slug}_module_manifest.json"
        status_path = PIPE / f"{spec.slug}_module_status.json"
        destination = PUBLISH_DIR / spec.slug
    require(not manifest_path.exists() and not status_path.exists(), "publication already exists", tag)
    require(not destination.exists(), "publication destination exists", tag)
    manifest_path.write_text(json.dumps(manifest, indent=2) + "\n")
    if amendment:
        n_local = len(manifest["amendment"]["local_declarations"])
        status = {
            "slice": manifest["slice"], "status": "PASS", "source_file": spec.source,
            "per_file": {spec.source: {
                "public_declarations": n - n_local, "local_declarations": n_local, "translated": n,
                "proof_clean": n, "semantic_proof_compiled": n, "certified": n,
                "status": ACCEPT_FILE, "published_at": now.isoformat()}},
            # no cumulative coverage: the public-declaration coverage of the chain is unchanged (a source-`Local`
            # lemma is not a public declaration)
            "amends_status": old_status.name, "amends_status_sha256": sha(old_status),
            "manifest_sha256": sha(manifest_path),
        }
    else:
        status = {
            "slice": manifest["slice"], "status": "PASS", "source_file": spec.source,
            "per_file": {spec.source: {
                "public_declarations": n, "translated": n, "proof_clean": n,
                "semantic_proof_compiled": n, "certified": n,
                "status": ACCEPT_FILE, "published_at": now.isoformat()}},
            "coverage": {
                "accepted_files": spec["previous_files"] + 1, "authoritative_files": AUTHORITATIVE["files"],
                "accepted_declarations": spec["previous_decls"] + n,
                "authoritative_declarations": AUTHORITATIVE["declarations"],
                "translated_but_not_certified": previous["coverage"]["translated_but_not_certified"],
                "deferred_external_boundary": previous["coverage"]["deferred_external_boundary"]},
            "previous_status_sha256": sha(previous_path) if previous_path else None,
            "manifest_sha256": sha(manifest_path),
        }
    status_path.write_text(json.dumps(status, indent=2) + "\n")
    (destination / "certificates").mkdir(parents=True)
    extra = [work / "source_extraction.json"] if mode == "extract" else []
    extra += [checkpoint_path] + ([provenance] if provenance.is_file() else [])
    for p in [exported, work / f"imported/Imported{name}.v", imported_vo, work / "export_metadata.json",
              work / "lean_type_audit.log", work / "lean_axiom_summary.json", work / "assumption_summary.json",
              work / "source_type_fingerprint.log", work / "source_build.log", work / "stage_timing.tsv",
              work / "imported_type_audit.log", source_vo, *extra]:
        shutil.copy2(p, destination / p.name)
    for m in modules:
        for suffix in (".v", ".vo"):
            shutil.copy2(work / "certificates" / f"{m}{suffix}", destination / "certificates" / f"{m}{suffix}")
    print(json.dumps({"manifest": str(manifest_path), "coverage": status.get("coverage", "unchanged (amendment)")},
                     indent=2))


def reprobe(spec: Spec) -> None:
    """Recompile only the source fingerprint probe in the existing run.

    For extracted sources the (display-only) probe is re-copied next to the
    unchanged extracted module, whose compiled .vo is reused as is."""
    require(spec["source_mode"] in ("pinned", "patched", "extract", "official_closure"), "reprobe: unknown source mode",
            spec.tag)
    src = spec.work / "source"
    if spec["source_mode"] == "extract":
        require((src / f"{spec['extraction']['module']}.vo").is_file(), "reprobe: extracted module not built",
                spec.tag)
        shutil.copy2(PROJECT / spec["fingerprint_probe"], src)
        (spec.work / "source_type_fingerprint.log").write_text("")
        require(rocq(["-R", str(src), "prosa", Path(spec["fingerprint_probe"]).name],
                     spec.work / "source_type_fingerprint.log", src, append=True) == 0,
                "fingerprint probe failed", spec.tag)
        print(f"{spec.tag}_REPROBE_PASS")
        return
    require(rocq(["-R", str(src), "prosa", str(PROJECT / spec["fingerprint_probe"])],
                 spec.work / "source_type_fingerprint.log", src) == 0, "fingerprint probe failed", spec.tag)
    print(f"{spec.tag}_REPROBE_PASS")


def main() -> None:
    spec = Spec(Path(sys.argv[1]).resolve())
    configure_family(spec)
    if spec.get("coqeal"):
        ROCQ_EXTRA[:] = ["-Q", str(spec.work / "coqeal/CoqEAL"), "CoqEAL"]
    stage = sys.argv[2]
    stages = {"prepare": [prepare], "check": [check], "publish": [publish], "reprobe": [reprobe],
              "all": [prepare, check, publish]}[stage]
    for fn in stages:
        fn(spec)


if __name__ == "__main__":
    main()
