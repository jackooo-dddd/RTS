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


class Rejected(SystemExit):
    pass


def require(cond: bool, msg: str, tag: str = "PIPELINE") -> None:
    if not cond:
        raise Rejected(f"{tag}_REJECTED: {msg}")


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


def rocq(args: list[str], log: Path, cwd: Path, append=False) -> int:
    return run(["opam", "exec", "--switch=rocq93rc1", "--", "rocq", "c", *args], log, cwd,
               append=append)


def lean_env(olean: Path) -> dict:
    env = dict(os.environ)
    env["LEAN_PATH"] = ":".join([str(olean)] + [
        str(PROJECT / f".lake/packages/{p}/.lake/build/lib/lean") for p in PACKAGES])
    env["ELAN_TOOLCHAIN"] = "leanprover/lean4:v4.33.1"
    return env


def accepted_status(source_file: str) -> str:
    for path in sorted(PIPE.glob("*status.json")):
        try:
            item = read(path).get("per_file", {}).get(source_file)
        except json.JSONDecodeError:
            continue
        if isinstance(item, dict) and item.get("status") == "ACCEPTED_V06_FILE":
            return path.name
    raise Rejected(f"PIPELINE_REJECTED: dependency not accepted: {source_file}")


def manifest_hash(stem: str, key: str) -> str:
    man = read(PIPE / f"{stem}_module_manifest.json")
    require(man.get("acceptance") == "ACCEPTED_V06_FILE", f"{stem} not accepted")
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
        self.work = EXP / f"{self.slug}_final"
        self.cert_dir = V / d["cert_dir"]
        self.fixtures = "Validation/fixtures/translation_order"

    def __getitem__(self, key):
        return self.d[key]

    def get(self, key, default=None):
        return self.d.get(key, default)


def inventory(spec: Spec) -> list[dict]:
    with (DEP / "declaration_inventory.csv").open() as stream:
        return [r for r in csv.DictReader(stream) if r["source_file"] == spec.source]


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


# --------------------------------------------------------------------------- prepare

def prepare(spec: Spec) -> None:
    import time
    tag, work = spec.tag, spec.work
    require(not work.exists(), f"{work} exists", tag)
    official = SOURCE_ROOT / spec.source
    with (DEP / "file_inventory.csv").open() as stream:
        row = next(r for r in csv.DictReader(stream) if r["file"] == spec.source)
    require(row["sha256"] == sha(official), "file inventory mismatch", tag)
    base = EXP / spec["base_run"]
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
    (work / "stage_timing.tsv").write_text("")
    t0 = time.time()

    # ---- source binding
    src = work / "source"
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
        require(rocq(["-R", str(src), "prosa", spec.source], log, src, append=True) == 0,
                "official source compile failed", tag)
        require(rocq(["-R", str(src), "prosa", str(PROJECT / spec["fingerprint_probe"])],
                     work / "source_type_fingerprint.log", src) == 0, "fingerprint probe failed", tag)
    elif mode == "extract":
        x = spec["extraction"]
        names = [r["declaration_name"] for r in inventory(spec)]
        # source-local helper blocks (e.g. #[local] instances) that the statements mention;
        # they must be byte-identical computational blocks (checked at publication)
        helper_blocks = x.get("helper_blocks", [])
        names = helper_blocks + names
        cmd = [sys.executable, str(V / "scripts/extract_v06_semantic_source.py"),
               "--source-root", str(SOURCE_ROOT), "--source-file", spec.source,
               "--module", x["module"], "--declarations", ",".join(names),
               "--elaborated-evidence", str(DEP / "declaration_type_evidence.json"),
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
    shutil.copytree(base / "olean/Prosa", olean / "Prosa")
    for art in spec.get("extra_olean_artifacts", []):
        dest = olean / art["to"]
        dest.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(EXP / art["from"], dest)
        require(sha(dest) == manifest_hash(art["manifest"], art["key"]), f"olean artifact changed: {art['to']}", tag)
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
    allowed_export_env = {"LEAN4EXPORT_PRESERVE_REDUCIBLE_THEOREM_TYPES"}
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
                                 "-Q imported FoundationImported", "-Q certificates FoundationCertificates"]})


def chain_key(previous_key: str, previous_vo: str | None, module: str, source: Path) -> str:
    return digest({"previous_key": previous_key, "previous_vo_sha256": previous_vo,
                   "module": module, "source_sha256": fsha(source)})


def checkpoint_valid(entry: dict | None, key: str, vo: Path, log: Path) -> bool:
    return bool(entry and entry.get("key") == key and vo.is_file() and log.is_file()
                and fsha(vo) == entry.get("vo_sha256") and fsha(log) == entry.get("log_sha256")
                and "Error" not in log.read_text(errors="replace"))


def exported_names(imported: Path) -> set[str]:
    """Rocq-side names (`A_B_c`) of every Lean name declared in the actual export files."""
    mangle = lambda n: "".join(c if c.isascii() else f"_UU{ord(c):04x}_" for c in n)
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
    evidence = read(DEP / "declaration_type_evidence.json")
    log = (spec.work / "source_type_fingerprint.log").read_text()
    require("Error" not in log, "Rocq source type audit failed", spec.tag)
    blocks = {m.group(1): " ".join(m.group(2).split())
              for m in re.finditer(r"(?ms)^BEGIN\|([^\n]+)\n(.*?)^END\|\1\s*$", log)}
    result = {}
    for row in rows:
        name = row["qualified_name"]
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
        matched_qualifier = False
        for qual in own_qualifiers:
            qualified = f"@{qual}.{short} : "
            if item["normalized_check"].startswith(qualified) and \
                    got == f"@{short} : " + item["normalized_check"][len(qualified):]:
                matched_qualifier = True
                break
        if matched_qualifier:
            result[name] = "EXACT_MODULO_OWN_MODULE_QUALIFIER"
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
        # file).  Accept exactly those recorded repairs, nothing else.
        own_names = {r["declaration_name"] for r in inventory(spec)}
        own_repairs = [tuple(r.split("=", 1)) for r in
                       (spec.get("extraction") or {}).get("printer_repairs", [])]
        own_repairs = [(old, new) for old, new in own_repairs
                       if new in own_names and any(old == f"{qual}.{new}" for qual in own_qualifiers)]
        repaired = ref
        for old, new in own_repairs:
            repaired = re.sub(rf"(?<![\w.']){re.escape(old)}(?![\w'])", new, repaired)
        result[name] = ("STATEMENT_BODY_EQUAL_TO_ELABORATED_TYPE" if body == ref
                        else "TYPE_EQUAL_MODULO_EXISTS_PARENS" if body is not None and body == unparen
                        and unparen != ref
                        else "TYPE_EQUAL_MODULO_MATHCOMP_ORDER_DEF_ABBREVIATION"
                        if body is not None and body == mc_order and mc_order != ref
                        else "STATEMENT_BODY_EQUAL_MODULO_OWN_MODULE_QUALIFIER"
                        if own_repairs and body is not None and body == repaired and repaired != ref
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
    if mode == "pinned":
        require(sha(copied) == sha(official), "compiled source copy is not byte-identical", tag)
        source_vo = copied.with_suffix(".vo")
        compat["note"] = "pinned source compiled byte-identically"
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
        require(sha(work / "olean" / art["to"]) == manifest_hash(art["manifest"], art["key"]),
                f"olean artifact changed: {art['to']}", tag)
    for lean_src, out, stem, *key in spec.get("extra_lean", []):
        if stem:
            require(sha(work / "olean" / out) == manifest_hash(stem, key[0] if key else "production_olean_sha256"),
                    f"dependency olean changed: {out}", tag)
    base = EXP / spec["base_run"]
    for check in spec["base_checks"]:
        if check.get("olean"):
            require(sha(work / "olean" / check["olean"]) ==
                    manifest_hash(check["manifest"], check.get("olean_key", "production_olean_sha256")),
                    f"dependency olean changed: {check['olean']}", tag)
        if check.get("vo"):
            require(sha(work / "source" / check["vo"]) ==
                    manifest_hash(check["manifest"], check.get("vo_key", "source_vo_sha256")),
                    f"dependency vo changed: {check['vo']}", tag)
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
    statement_only = [ns + n for n in targets if n not in computational]
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
    mangle = lambda n: "".join(c if c.isascii() else f"_UU{ord(c):04x}_" for c in n)
    require("Error" not in type_audit and all(prefix + mangle(n) in type_audit for n in targets),
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
    expected = {c for n in targets for c in principal.get(n, [f"{n}_correspondence"])} | set(spec["helpers"])
    require(summary["audit_policy"] == "fail_closed"
            and set(summary["certificates"]) == set(aconf["certificates"]) == expected
            and aconf["statement_only_dependencies"] == [], "assumption summary incomplete", tag)
    for item in summary["certificates"].values():
        require(item["status"] in {"CERTIFIED", "CERTIFIED_WITH_PROP_SPROP_FOUNDATION"}
                and not item["semantic_premises"] and not item["statement_only_dependencies"]
                and not item["unexpected"] and not item["source_theorem_dependency"]
                and not item["target_theorem_dependency"], "Rocq semantic gate failed", tag)

    # baseline
    previous_path = PIPE / spec["previous_status"]
    previous = read(previous_path)
    require(previous["status"] == "PASS"
            and previous["coverage"]["accepted_files"] == spec["previous_files"]
            and previous["coverage"]["accepted_declarations"] == spec["previous_decls"],
            "formal baseline changed", tag)
    require(not git(ROOT, "status", "--porcelain", "--", "Prosa-fei"), "Prosa-fei changed", tag)

    now = datetime.now(timezone.utc).astimezone()
    declarations = []
    for r in rows:
        n = r["declaration_name"]
        certs = principal.get(n, [f"{n}_correspondence"])
        statuses = {summary["certificates"][c]["status"] for c in certs}
        declarations.append({
            "source_declaration": r["qualified_name"], "lean_declaration": ns + n,
            "semantic_status": "CERTIFIED_WITH_PROP_SPROP_FOUNDATION"
            if "CERTIFIED_WITH_PROP_SPROP_FOUNDATION" in statuses else "CERTIFIED",
            "certificates": certs, "semantic_premises": [],
            "source_theorem_dependency": False, "target_theorem_dependency": False,
            "acceptance": "ACCEPTED_V06_TRANSLATION"})
    timing = [l.split("\t") for l in (work / "stage_timing.tsv").read_text().splitlines()]
    export_lines = sum(1 for _ in exported.open("rb"))
    manifest = {
        "slice": "TRANSLATION_ORDER_" + spec.slug.upper(),
        "generated_at": now.isoformat(), "published_at": now.isoformat(),
        "rank": spec["rank"], "layer": spec["layer"], "source_file": spec.source,
        "source_commit": PIN, "source_tree": TREE, "source_file_sha256": sha(official),
        "pipeline": "Validation/scripts/translation_file_pipeline.py",
        "spec": str(spec.path.relative_to(PROJECT)), "spec_sha256": sha(spec.path),
        "source_compatibility": compat, "source_type_evidence": matches,
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
        "declarations": declarations, "acceptance": "ACCEPTED_V06_FILE",
    }
    manifest_path = PIPE / f"{spec.slug}_module_manifest.json"
    status_path = PIPE / f"{spec.slug}_module_status.json"
    require(not manifest_path.exists() and not status_path.exists(), "publication already exists", tag)
    destination = V / "imported/translation_order" / spec.slug
    require(not destination.exists(), "publication destination exists", tag)
    manifest_path.write_text(json.dumps(manifest, indent=2) + "\n")
    n = len(targets)
    status = {
        "slice": manifest["slice"], "status": "PASS", "source_file": spec.source,
        "per_file": {spec.source: {
            "public_declarations": n, "translated": n, "proof_clean": n,
            "semantic_proof_compiled": n, "certified": n,
            "status": "ACCEPTED_V06_FILE", "published_at": now.isoformat()}},
        "coverage": {
            "accepted_files": spec["previous_files"] + 1, "authoritative_files": 357,
            "accepted_declarations": spec["previous_decls"] + n, "authoritative_declarations": 2439,
            "translated_but_not_certified": previous["coverage"]["translated_but_not_certified"],
            "deferred_external_boundary": previous["coverage"]["deferred_external_boundary"]},
        "previous_status_sha256": sha(previous_path), "manifest_sha256": sha(manifest_path),
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
    print(json.dumps({"manifest": str(manifest_path), "coverage": status["coverage"]}, indent=2))


def reprobe(spec: Spec) -> None:
    """Recompile only the source fingerprint probe in the existing run.

    For extracted sources the (display-only) probe is re-copied next to the
    unchanged extracted module, whose compiled .vo is reused as is."""
    require(spec["source_mode"] in ("pinned", "patched", "extract"), "reprobe: unknown source mode", spec.tag)
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
    stage = sys.argv[2]
    stages = {"prepare": [prepare], "check": [check], "publish": [publish], "reprobe": [reprobe],
              "all": [prepare, check, publish]}[stage]
    for fn in stages:
        fn(spec)


if __name__ == "__main__":
    main()
