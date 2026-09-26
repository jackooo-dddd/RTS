#!/usr/bin/env python3
"""Fail-closed validation and publication of a zero-declaration aggregation module.

Mirrors the accepted behavior/all.v treatment: the authoritative module has no
named declarations; it is accepted when (1) the pinned source and the empty
inventory entry match, (2) its only content is the `Require Export` list and
the Lean aggregator imports exactly the corresponding translated modules,
(3) every direct dependency is accepted and hash-bound, (4) the byte-identical
source compiles on a verified dependency closure, and (5) the Lean aggregator
and an aggregator-only interface probe compile with a clean axiom audit.

Usage: validate_zero_declaration_aggregation.py <spec.json>
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
from datetime import datetime, timezone
from pathlib import Path

PROJECT = Path(__file__).resolve().parents[2]
ROOT = PROJECT.parent
V = PROJECT / "Validation"
PIPE = V / "planning/v06_pipeline"
PIN = "414e66760333eaa4ef78c685bcf53291c527a548"


def require(cond: bool, msg: str) -> None:
    if not cond:
        raise SystemExit("ZERO_DECL_REJECTED: " + msg)


def sha(path: Path) -> str:
    require(path.is_file() and path.stat().st_size > 0, f"missing/empty {path}")
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read(path: Path) -> dict:
    return json.loads(path.read_text())


def accepted_status(source_file: str) -> str:
    for path in sorted(PIPE.glob("*status.json")):
        item = read(path).get("per_file", {}).get(source_file)
        if isinstance(item, dict) and item.get("status") == "ACCEPTED_V06_FILE":
            return path.name
    raise SystemExit(f"ZERO_DECL_REJECTED: dependency not accepted: {source_file}")


def strip_comments(text: str) -> str:
    out, depth, i = [], 0, 0
    while i < len(text):
        if text.startswith("(*", i):
            depth += 1; i += 2; continue
        if depth and text.startswith("*)", i):
            depth -= 1; i += 2; continue
        if not depth:
            out.append(text[i])
        i += 1
    return "".join(out)


def main() -> None:
    spec = read(Path(sys.argv[1]))
    source_file = spec["source"]
    source_root = V / ".work/prosa-v06-414e667"
    official = source_root / source_file
    work = V / ".work/experiments" / (spec["slug"] + "_final")
    require(not work.exists(), f"{work} exists")
    require(subprocess.check_output(["git", "-C", str(source_root), "rev-parse", "HEAD"],
                                    text=True).strip() == PIN, "source commit changed")

    with (V / "planning/v06_dependency/file_inventory.csv").open() as stream:
        row = next(r for r in csv.DictReader(stream) if r["file"] == source_file)
    require(row["sha256"] == sha(official), "file inventory mismatch")
    with (V / "planning/v06_dependency/declaration_inventory.csv").open() as stream:
        require(not [r for r in csv.DictReader(stream) if r["source_file"] == source_file],
                "inventory lists declarations for a zero-declaration module")
    dag = read(V / "planning/v06_dependency/file_dag.json")
    deps = {e["dependency_file"] for e in dag["edges"] if e["dependent_file"] == source_file}
    require(deps == set(spec["dependencies"]), f"file DAG changed: {sorted(deps)}")
    dependency_evidence = {d: accepted_status(d) for d in sorted(deps)}

    # Exact re-export mapping (source content is only the export list).
    source_text = strip_comments(official.read_text())
    lines = [l.strip() for l in source_text.splitlines() if l.strip()]
    exports = [m.group(1) for l in lines for m in [re.fullmatch(r"Require Export (prosa\.[\w.]+)\.", l)] if m]
    require(len(exports) == len(lines), "source contains more than its Require Export list")
    require(exports == list(spec["export_map"]), f"source export list changed: {exports}")
    production = PROJECT / spec["production"]
    lean_text = production.read_text()
    imports = re.findall(r"^import (\S+)$", lean_text, re.M)
    require(imports == list(spec["export_map"].values()), f"Lean imports differ: {imports}")
    require(not re.search(r"^\s*(def|theorem|lemma|instance|abbrev|structure|class|inductive|axiom)\b",
                          lean_text, re.M), "Lean aggregator declares something")
    require(not re.search(r"\b(sorry|admit|axiom|unsafe)\b", lean_text), "forbidden Lean escape")

    work.mkdir(parents=True)
    t0 = datetime.now()
    # Source: verified accepted closure + byte-identical module.
    closure = V / ".work/experiments" / spec["source_closure_run"] / "source"
    shutil.copytree(closure, work / "source")
    for dep, (stem, rel_vo) in spec["dependency_source_vo"].items():
        man = read(PIPE / f"{stem}_module_manifest.json")
        want = man.get("source_vo_sha256") or man.get("artifact_hashes", {}).get("source_vo")
        require(sha(work / "source" / rel_vo) == want, f"dependency source .vo changed: {dep}")
    target = work / "source" / source_file
    target.parent.mkdir(parents=True, exist_ok=True)
    shutil.copy2(official, target)
    env = dict(os.environ)
    res = subprocess.run(["opam", "exec", "--switch=rocq93rc1", "--", "rocq", "c", "-R",
                          str(work / "source"), "prosa", source_file],
                         cwd=work / "source", capture_output=True, text=True)
    (work / "source_build.log").write_text(res.stdout + res.stderr)
    require(res.returncode == 0 and "Error" not in res.stdout + res.stderr, "official source compile failed")
    source_vo = target.with_suffix(".vo")
    require(sha(target) == sha(official) and sha(source_vo), "source copy/vo check failed")

    # Lean: verified dependency oleans + fresh aggregator and interface probe.
    shutil.copytree(V / ".work/experiments" / spec["olean_closure_run"] / "olean", work / "olean")
    for dep, (stem, rel_olean) in spec["dependency_olean"].items():
        man = read(PIPE / f"{stem}_module_manifest.json")
        want = man.get("production_olean_sha256") or man.get("artifact_hashes", {}).get("production_olean")
        require(sha(work / "olean" / rel_olean) == want, f"dependency olean changed: {dep}")
    pkgs = ":".join(str(PROJECT / f".lake/packages/{p}/.lake/build/lib/lean") for p in
                    ["mathlib", "plausible", "proofwidgets", "batteries", "aesop", "importGraph",
                     "LeanSearchClient", "Qq", "Cli"])
    env["LEAN_PATH"] = f"{work / 'olean'}:{pkgs}"
    env["ELAN_TOOLCHAIN"] = "leanprover/lean4:v4.33.1"
    prod_olean = work / "olean" / spec["production_olean"]
    prod_olean.parent.mkdir(parents=True, exist_ok=True)
    res = subprocess.run(["lean", "-DautoImplicit=false", "-R", str(PROJECT), "-o", str(prod_olean),
                          spec["production"]], cwd=PROJECT, env=env, capture_output=True, text=True)
    (work / "lean_build.log").write_text(res.stdout + res.stderr)
    require(res.returncode == 0 and "error" not in (res.stdout + res.stderr).lower(), "Lean aggregator build failed")
    fx_olean = work / "olean" / (spec["fixture_module"].replace(".", "/") + ".olean")
    fx_olean.parent.mkdir(parents=True, exist_ok=True)
    res = subprocess.run(["lean", "-DautoImplicit=false", "-R", str(PROJECT), "-o", str(fx_olean),
                          spec["fixture"]], cwd=PROJECT, env=env, capture_output=True, text=True)
    log = res.stdout + res.stderr
    (work / "interface.log").write_text(log)
    require(res.returncode == 0 and "error" not in log.lower(), "interface probe build failed")
    require(f"'{spec['probe_decl']}' does not depend on any axioms" in log
            or all(a in spec.get("probe_allowed_axioms", []) for a in
                   re.findall(r"depends on axioms: \[(.*?)\]", log)[0].split(", ")),
            "interface probe axiom audit failed")
    elapsed = int((datetime.now() - t0).total_seconds())

    previous_path = PIPE / spec["previous_status"]
    previous = read(previous_path)
    require(previous["status"] == "PASS"
            and previous["coverage"]["accepted_files"] == spec["previous_files"]
            and previous["coverage"]["accepted_declarations"] == spec["previous_decls"],
            "formal baseline changed")
    require(not subprocess.check_output(["git", "-C", str(ROOT), "status", "--porcelain", "--", "Prosa-fei"],
                                        text=True).strip(), "historical Prosa-fei workspace changed")
    now = datetime.now(timezone.utc).astimezone()
    manifest = {
        "slice": "TRANSLATION_ORDER_" + spec["slug"].upper(),
        "generated_at": now.isoformat(), "published_at": now.isoformat(),
        "rank": spec["rank"], "layer": spec["layer"], "source_file": source_file,
        "source_commit": PIN, "source_file_sha256": sha(official),
        "public_declaration_count": 0,
        "export_mapping": spec["export_map"],
        "production_file": spec["production"], "production_source_sha256": sha(production),
        "production_olean_sha256": sha(prod_olean),
        "interface_fixture": spec["fixture"], "interface_fixture_source_sha256": sha(PROJECT / spec["fixture"]),
        "interface_fixture_olean_sha256": sha(fx_olean), "interface_probe": spec["probe_decl"],
        "official_source_vo_sha256": sha(source_vo),
        "file_dependencies": dependency_evidence,
        "cross_itp_declaration_validation": {
            "applicability": "NOT_APPLICABLE_NO_NAMED_SOURCE_DECLARATIONS",
            "lean4export_executions": 0, "rocq_import_executions": 0, "semantic_certificates": 0,
            "reason": ("The authoritative module declares no named object. Its observable aggregation "
                       "boundary is validated from its accepted dependencies, the byte-identical compiled "
                       "Rocq module, and an actual compiled Lean aggregator-only interface probe.")},
        "notes": spec.get("notes", ""),
        "elapsed_seconds": elapsed,
        "acceptance": "ACCEPTED_V06_FILE",
    }
    manifest_path = PIPE / f"{spec['slug']}_module_manifest.json"
    status_path = PIPE / f"{spec['slug']}_module_status.json"
    require(not manifest_path.exists() and not status_path.exists(), "publication already exists")
    manifest_path.write_text(json.dumps(manifest, indent=2) + "\n")
    status = {
        "slice": manifest["slice"], "status": "PASS", "source_file": source_file,
        "per_file": {source_file: {
            "public_declarations": 0, "translated": 0, "proof_clean": 0, "certified": 0,
            "module_interface_audited": True, "direct_dependencies_accepted": len(deps),
            "status": "ACCEPTED_V06_FILE",
            "reason": "zero-declaration aggregation module; exact re-export mapping, accepted dependency/hash closure, official Rocq compile, and actual compiled Lean interface all passed",
            "published_at": now.isoformat()}},
        "coverage": {
            "accepted_files": spec["previous_files"] + 1, "authoritative_files": 357,
            "accepted_declarations": spec["previous_decls"], "authoritative_declarations": 2439,
            "translated_but_not_certified": previous["coverage"]["translated_but_not_certified"],
            "deferred_external_boundary": previous["coverage"]["deferred_external_boundary"]},
        "previous_status_sha256": sha(previous_path), "manifest_sha256": sha(manifest_path),
    }
    status_path.write_text(json.dumps(status, indent=2) + "\n")
    dest = V / "imported/translation_order" / spec["slug"]
    require(not dest.exists(), "publication destination exists")
    dest.mkdir(parents=True)
    for p in (source_vo, work / "source_build.log", work / "lean_build.log", work / "interface.log"):
        shutil.copy2(p, dest / p.name)
    print(json.dumps({"manifest": str(manifest_path), "coverage": status["coverage"]}, indent=2))


if __name__ == "__main__":
    main()
