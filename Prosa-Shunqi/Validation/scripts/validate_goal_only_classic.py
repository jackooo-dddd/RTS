#!/usr/bin/env python3
"""Fail-closed goal-only validation and publication of a classic *example* file (user decision 2026-10-03).

The classic example files (`classic/implementation/**/*_example.v`) state closed results about concrete task sets,
built from section-local `Let`s of concrete records; there is no input to relate, and their Lean translations use
concrete Lean structures.  As for the v0.6 goal-only example module (user-authorized 2026-10-01), such a file is
accepted without cross-ITP correspondence certificates when

 (1) the pinned source matches the file inventory (full classic scope) and the pinned ProsaBuddy commit;
 (2) every direct dependency is accepted (classic chain, or v0.6 chain for util files);
 (3) the byte-identical source compiles on its verified official proof closure: each closure file is copied from the
     pinned tree (hash-checked), the recorded compatibility patches of the closure files are applied (and are the only
     differences; the module itself is never patched), and every file compiles in dependency order under the pinned
     Rocq switch with the recorded classic compatibility prelude;
 (4) the Lean translation declares every inventory declaration of the file (same module path and short name), uses no
     escape (`sorry`, `admit`, `axiom`, `unsafe`, `native_decide`, `implemented_by`, `extern`), every imported
     accepted classic translation is byte-identical to its accepted manifest, the module builds, and every inventory
     declaration passes the Lean axiom audit (standard axioms only).

Nothing is certified: the publication records the file as ACCEPTED_CLASSIC_FILE in acceptance mode GOAL_ONLY, adds
the file to `accepted_files`, and counts its declarations in `goal_only_declarations` (never in
`accepted_declarations`, which counts certified declarations only).

Usage: validate_goal_only_classic.py RANK [--publish]
"""

from __future__ import annotations

import csv
import hashlib
import json
import re
import shutil
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path

PROJECT = Path(__file__).resolve().parents[1].parent
V = PROJECT / "Validation"
CSV_PATH = PROJECT / "classic-prosa/comprehensive-classic/file_order.csv"
DEP = V / "planning/classic_full_dependency"
PIPE = V / "planning/classic_pipeline"
V06_PIPE = V / "planning/v06_pipeline"
SOURCE_ROOT = V / ".work/prosabuddy-f692cb7/prosaworkspace"
PIN = "f692cb7479780cf6009493f373a309e13165201c"
PRELUDE = PROJECT / "classic-prosa/rocq93-port/Rocq90Compat.v"
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
LEAN_ESCAPES = r"\b(sorry|admit|axiom|unsafe|native_decide|implemented_by|extern)\b"


def require(cond: bool, msg: str) -> None:
    if not cond:
        raise SystemExit("GOAL_ONLY_CLASSIC_REJECTED: " + msg)


def sha(path: Path) -> str:
    require(path.is_file() and path.stat().st_size > 0, f"missing/empty {path}")
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read(path: Path) -> dict:
    return json.loads(path.read_text())


def accepted(source_file: str) -> str:
    chains = [(PIPE, "ACCEPTED_CLASSIC_FILE"), (V06_PIPE, "ACCEPTED_V06_FILE")]
    for pipe, label in chains:
        for path in sorted(pipe.glob("*status.json")):
            try:
                item = read(path).get("per_file", {}).get(source_file)
            except json.JSONDecodeError:
                continue
            if isinstance(item, dict) and item.get("status") == label:
                return f"{pipe.name}/{path.name}"
    raise SystemExit(f"GOAL_ONLY_CLASSIC_REJECTED: dependency not accepted: {source_file}")


def closure_of(source: str, edges: list[dict]) -> list[str]:
    """Dependency-ordered transitive closure (as scripts/classic_mkfile.py), the module last."""
    deps: dict[str, list[str]] = {}
    for e in edges:
        deps.setdefault(e["dependent_file"], []).append(e["dependency_file"])
    order: list[str] = []
    seen: set[str] = set()

    def visit(f: str) -> None:
        if f in seen:
            return
        seen.add(f)
        for d in sorted(deps.get(f, [])):
            visit(d)
        order.append(f)
    visit(source)
    return order


def latest_status() -> Path:
    best = None
    for p in PIPE.glob("*_module_status.json"):
        d = read(p)
        if d.get("status") == "PASS" and d.get("coverage", {}).get("authoritative_files") == 190:
            k = (d["coverage"]["accepted_declarations"], d["coverage"]["accepted_files"])
            if best is None or k > best[0]:
                best = (k, p)
    require(best is not None, "no full-scope classic status")
    return best[1]


def rocq(args: list[str], cwd: Path) -> subprocess.CompletedProcess:
    return subprocess.run(["zsh", "-c", 'ulimit -s 65520 && exec opam exec --switch=rocq93rc1 -- rocq c "$@"', "rocq",
                           *args], cwd=cwd, capture_output=True, text=True)


def main() -> None:
    rank = int(sys.argv[1])
    publish = "--publish" in sys.argv[2:]
    with CSV_PATH.open() as stream:
        row = next(r for r in csv.DictReader(stream) if int(r["rank"]) == rank)
    source_file, production = row["source"], row["lean_target"]
    require(source_file.startswith("classic/implementation/") and source_file.endswith("_example.v"),
            "goal-only mode is restricted to classic example files")
    slug = source_file[:-2].replace("/", "_")
    official = SOURCE_ROOT / source_file
    require(subprocess.check_output(["git", "-C", str(SOURCE_ROOT.parent), "rev-parse", "HEAD"],
                                    text=True).strip() == PIN, "source commit changed")
    with (DEP / "file_inventory.csv").open() as stream:
        inventory = {r["file"]: r for r in csv.DictReader(stream)}
    require(inventory[source_file]["sha256"] == sha(official) == row["sha256"], "file inventory mismatch")
    with (DEP / "declaration_inventory.csv").open() as stream:
        decls = [r for r in csv.DictReader(stream) if r["source_file"] == source_file]
    require(decls, "no inventory declarations")
    edges = read(DEP / "file_dag.json")["edges"]
    deps = sorted({e["dependency_file"] for e in edges if e["dependent_file"] == source_file})
    dependency_evidence = {d: accepted(d) for d in deps}

    # (3) official proof closure + byte-identical module
    work = V / ".work/experiments" / (slug + "_goalonly")
    if work.exists():
        shutil.rmtree(work)
    src = work / "source"
    src.mkdir(parents=True)
    closure = closure_of(source_file, edges)
    require(closure[-1] == source_file, "closure malformed")
    umap = read(V / "patches/classic/util_patch_map.json")
    patches = [p for f in closure for p in umap.get(f, [])]
    for rel in closure:
        require(inventory[rel]["sha256"] == sha(SOURCE_ROOT / rel), f"pinned closure file changed: {rel}")
        (src / rel).parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(SOURCE_ROOT / rel, src / rel)
    patched: set[str] = set()
    for patch in patches:
        touched = re.findall(r"^\+\+\+ b/(\S+)", (V / patch).read_text(), re.M)
        require(all(t in closure for t in touched), f"patch touches a file outside the closure: {patch}")
        require(source_file not in touched, "the module itself must not be patched")
        subprocess.run(["patch", "-s", "-p1", "-i", str(V / patch)], cwd=src, check=True)
        patched |= set(touched)
    for rel in closure:
        require((sha(src / rel) == sha(SOURCE_ROOT / rel)) == (rel not in patched),
                f"closure file differs from the pinned file without a recorded patch: {rel}")
    require(sha(PRELUDE) == read(DEP / "prelude.json")["sha256"], "compatibility prelude changed")
    (work / "compat").mkdir()
    shutil.copy2(PRELUDE, work / "compat/Rocq90Compat.v")
    res = rocq(["-Q", str(work / "compat"), "Compat", "Rocq90Compat.v"], work / "compat")
    require(res.returncode == 0, "compatibility prelude compile failed")
    vo: dict[str, str] = {}
    build_log = work / "closure_build.log"
    with build_log.open("w") as log:
        for rel in closure:
            flags = ["-ri", "Compat.Rocq90Compat"] if rel.startswith("classic/") else []
            res = rocq(["-Q", str(work / "compat"), "Compat", "-R", str(src), "prosa", *flags, rel], src)
            log.write(f"== {rel} rc={res.returncode}\n{res.stdout}{res.stderr}")
            require(res.returncode == 0 and "Error" not in res.stdout + res.stderr, f"closure compile failed: {rel}")
            vo[rel] = sha((src / rel).with_suffix(".vo"))
    require(sha(src / source_file) == sha(official), "module copy differs from the pinned source")

    # (4) Lean translation: declarations, escapes, accepted imports, build, axiom audit
    lean_path = PROJECT / production
    lean_text = lean_path.read_text()
    lean_code = re.sub(r"--[^\n]*", "", re.sub(r"/-.*?-/", "", lean_text, flags=re.S))
    require(not re.search(LEAN_ESCAPES, lean_code), "forbidden Lean escape")
    namespaces = re.findall(r"^namespace (\S+)", lean_code, re.M)
    lean_names = {}
    for r in decls:
        module, short = r["declaration_name"].rsplit(".", 1) if "." in r["declaration_name"] else ("", r["declaration_name"])
        ns = [n for n in namespaces if not module or n.endswith("." + module) or n == module]
        require(ns, f"no Lean namespace for {r['declaration_name']}")
        require(re.search(rf"^(?:private\s+)?(?:noncomputable\s+)?(theorem|def|abbrev|lemma|instance)\s+{re.escape(short)}\b",
                          lean_code, re.M), f"Lean translation lacks {r['declaration_name']}")
        lean_names[r["declaration_name"]] = f"{ns[0]}.{short}"
    imports = re.findall(r"^import (\S+)", lean_code, re.M)
    with CSV_PATH.open() as stream:
        by_target = {r["lean_target"]: r for r in csv.DictReader(stream)}
    import_evidence = {}
    for imp in imports:
        target = imp.replace(".", "/") + ".lean"
        r = by_target.get(target)
        if r is None:
            continue
        mpath = PIPE / f"{r['source'][:-2].replace('/', '_')}_module_manifest.json"
        require(mpath.is_file(), f"no accepted manifest for imported translation {target}")
        m = read(mpath)
        require(m.get("production_source_sha256") == sha(PROJECT / target),
                f"imported translation differs from its accepted manifest: {target}")
        import_evidence[target] = m["production_source_sha256"]
    module = production[:-len(".lean")].replace("/", ".")
    res = subprocess.run(["lake", "build", module], cwd=PROJECT, capture_output=True, text=True)
    (work / "lean_build.log").write_text(res.stdout + res.stderr)
    require(res.returncode == 0, "Lean build failed")
    olean = PROJECT / ".lake/build/lib/lean" / (production[:-len(".lean")] + ".olean")
    audit = work / "LeanAxiomAudit.lean"
    audit.write_text(f"import {module}\n" + "".join(f"#print axioms {n}\n" for n in lean_names.values()))
    res = subprocess.run(["lake", "env", "lean", str(audit)], cwd=PROJECT, capture_output=True, text=True)
    log = res.stdout + res.stderr
    (work / "lean_axiom_audit.log").write_text(log)
    require(res.returncode == 0 and "error" not in log.lower(), "Lean axiom audit failed to run")
    axioms = {}
    for rocq_name, n in lean_names.items():
        m = re.search(rf"'{re.escape(n)}' (does not depend on any axioms|depends on axioms: \[(.*?)\])", log, re.S)
        require(m is not None, f"no axiom report for {n}")
        found = [a.strip() for a in (m.group(2) or "").split(",") if a.strip()]
        require(set(found) <= ALLOWED_AXIOMS, f"unexpected axioms in {n}: {found}")
        axioms[rocq_name] = {"lean_name": n, "axioms": found}
    report = {"rank": rank, "source_file": source_file, "declarations": len(decls), "closure_files": len(closure),
              "patched_closure_files": sorted(patched), "dependencies": dependency_evidence}
    print(json.dumps(report, indent=2))
    if not publish:
        print("GOAL_ONLY_CLASSIC_PASS (not published)")
        return

    # publication
    previous_path = latest_status()
    previous = read(previous_path)
    now = datetime.now(timezone.utc).astimezone()
    manifest = {
        "slice": "CLASSIC_TRANSLATION_ORDER_" + slug.upper(),
        "generated_at": now.isoformat(), "published_at": now.isoformat(),
        "rank": rank, "layer": int(row["layer"]), "source_file": source_file, "source_commit": PIN,
        "source_file_sha256": sha(official), "public_declaration_count": len(decls),
        "acceptance_mode": "GOAL_ONLY_CLASSIC_EXAMPLE (user decision 2026-10-03)",
        "official_proof_closure": {
            "files": closure, "patches": {p: sha(V / p) for p in patches}, "patched_files": sorted(patched),
            "prelude_sha256": sha(PRELUDE), "vo_sha256": vo},
        "official_source_vo_sha256": vo[source_file],
        "production_file": production, "production_source_sha256": sha(lean_path),
        "production_olean_sha256": sha(olean), "imported_translation_sha256": import_evidence,
        "lean_declarations": axioms, "file_dependencies": dependency_evidence,
        "cross_itp_declaration_validation": {
            "applicability": "GOAL_ONLY_CONCRETE_EXAMPLE",
            "semantic_certificates": 0,
            "reason": ("Concrete example file (closed results about concrete task sets, no inputs to relate). The "
                       "byte-identical official module is compiled on its verified official proof closure; each "
                       "inventory declaration has a Lean translation that compiles with a clean axiom audit. No "
                       "Rocq-Lean correspondence certificate is claimed.")},
        "acceptance": "ACCEPTED_CLASSIC_FILE",
    }
    manifest_path = PIPE / f"{slug}_module_manifest.json"
    status_path = PIPE / f"{slug}_module_status.json"
    require(not manifest_path.exists() and not status_path.exists(), "publication already exists")
    manifest_path.write_text(json.dumps(manifest, indent=2) + "\n")
    cov = dict(previous["coverage"])
    cov["accepted_files"] = cov["accepted_files"] + 1
    # goal-only declarations are tallied from the goal-only manifests (certified publications do not carry the key)
    cov["goal_only_declarations"] = sum(
        read(m).get("public_declaration_count", 0) for m in PIPE.glob("*_module_manifest.json")
        if str(read(m).get("acceptance_mode", "")).startswith("GOAL_ONLY_CLASSIC_EXAMPLE"))
    status = {
        "slice": manifest["slice"], "status": "PASS", "source_file": source_file,
        "per_file": {source_file: {
            "public_declarations": len(decls), "translated": len(decls), "proof_clean": len(decls), "certified": 0,
            "goal_only_example_audited": True, "direct_dependencies_accepted": len(deps),
            "status": "ACCEPTED_CLASSIC_FILE", "acceptance_mode": "GOAL_ONLY",
            "reason": ("goal-only classic example; byte-identical official module compiled on the verified official "
                       "proof closure, Lean declarations compiled with a clean axiom audit; no certificates"),
            "published_at": now.isoformat()}},
        "coverage": cov,
        "previous_status_sha256": sha(previous_path), "manifest_sha256": sha(manifest_path),
    }
    status_path.write_text(json.dumps(status, indent=2) + "\n")
    dest = V / "imported/classic_translation_order" / slug
    if dest.exists():
        shutil.rmtree(dest)
    dest.mkdir(parents=True)
    for p in ((src / source_file).with_suffix(".vo"), build_log, work / "lean_build.log", work / "lean_axiom_audit.log"):
        shutil.copy2(p, dest / p.name)
    print(json.dumps({"manifest": str(manifest_path), "coverage": cov}, indent=2))


if __name__ == "__main__":
    main()
