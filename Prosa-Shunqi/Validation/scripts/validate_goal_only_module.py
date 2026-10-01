#!/usr/bin/env python3
"""Fail-closed validation and publication of a goal-only example module (user-authorized mode, 2026-10-01).

A goal-only module declares no named object; besides its `Require Import` list it contains one Section with
`Context`/`Variable`/`Hypothesis` inputs and anonymous `Goal`s closed by proof scripts. It is accepted when
 (1) the pinned source and its empty inventory entry match, and its content is exactly of that shape with the
     recorded number of goals;
 (2) every direct dependency is accepted;
 (3) the byte-identical source compiles on a verified *official proof closure*: each closure file is copied from the
     pinned tree (hash-checked against the file inventory), the recorded compatibility patch(es) are applied (and are
     the only differences; the module itself is never patched), and every file compiles in the recorded order under
     the pinned Rocq switch;
 (4) the Lean translation states each goal as a named theorem (`goal_1` ... `goal_n`, source order), uses no escape,
     compiles on hash-checked accepted dependency oleans, and every theorem passes the axiom audit (standard Lean
     axioms only).
Nothing is certified: there is no named source declaration.

Usage: validate_goal_only_module.py <spec.json>
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
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
PACKAGES = ["mathlib", "plausible", "proofwidgets", "batteries", "aesop", "importGraph", "LeanSearchClient", "Qq",
            "Cli"]


def require(cond: bool, msg: str) -> None:
    if not cond:
        raise SystemExit("GOAL_ONLY_REJECTED: " + msg)


def sha(path: Path) -> str:
    require(path.is_file() and path.stat().st_size > 0, f"missing/empty {path}")
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read(path: Path) -> dict:
    return json.loads(path.read_text())


def accepted_status(source_file: str) -> str:
    for path in sorted(PIPE.glob("*status.json")):
        try:
            item = read(path).get("per_file", {}).get(source_file)
        except json.JSONDecodeError:
            continue
        if isinstance(item, dict) and item.get("status") == "ACCEPTED_V06_FILE":
            return path.name
    raise SystemExit(f"GOAL_ONLY_REJECTED: dependency not accepted: {source_file}")


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


def manifest_olean(stem: str) -> str:
    man = read(PIPE / f"{stem}_module_manifest.json")
    require(man.get("acceptance") == "ACCEPTED_V06_FILE", f"{stem} not accepted")
    return man.get("production_olean_sha256") or man.get("artifact_hashes", {}).get("production_olean")


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
        inventory = {r["file"]: r for r in csv.DictReader(stream)}
    require(inventory[source_file]["sha256"] == sha(official), "file inventory mismatch")
    with (V / "planning/v06_dependency/declaration_inventory.csv").open() as stream:
        require(not [r for r in csv.DictReader(stream) if r["source_file"] == source_file],
                "inventory lists declarations for a goal-only module")
    dag = read(V / "planning/v06_dependency/file_dag.json")
    deps = {e["dependency_file"] for e in dag["edges"] if e["dependent_file"] == source_file}
    require(deps == set(spec["dependencies"]), f"file DAG changed: {sorted(deps)}")
    dependency_evidence = {d: accepted_status(d) for d in sorted(deps)}

    # (1) shape: Require Import list, one Section of inputs, anonymous Goals with proofs.
    text = strip_comments(official.read_text())
    sentences = [s.strip() for s in re.split(r"(?<=\.)\s+", text) if s.strip()]
    kinds, in_proof = [], False
    for s in sentences:
        if in_proof:                      # the proof script of a goal: checked by compiling the module
            if s == "Qed.":
                in_proof = False
                kinds.append("Qed")
            continue
        m = re.match(r"(#\[[^\]]*\]\s*)?(\w+)", s)
        kinds.append(m.group(2) if m else s)
        if s == "Proof." or s.startswith("Proof. "):
            in_proof = True
            if s.endswith(" Qed."):
                in_proof = False
                kinds.append("Qed")
    imports = [s for s in sentences if s.startswith("Require Import ")]
    require([re.fullmatch(r"Require Import (prosa\.[\w.]+)\.", s).group(1) for s in imports]
            == spec["imports"], "source import list changed")
    allowed = {"Require", "Section", "End", "Context", "Variable", "Hypothesis", "Goal", "Proof", "Qed"}
    require(set(kinds) <= allowed, f"unexpected source commands: {sorted(set(kinds) - allowed)}")
    require(kinds.count("Section") == 1 and kinds.count("End") == 1, "expected exactly one Section")
    goals = [s for s in sentences if s.startswith("Goal ")]
    require(len(goals) == spec["goal_count"] == kinds.count("Qed") == kinds.count("Proof"),
            f"goal count changed: {len(goals)}")

    # (3) official proof closure + byte-identical module.
    closure = (V / spec["closure_files"]).read_text().split()
    require(closure[-1] == source_file and len(set(closure)) == len(closure), "closure list malformed")
    src = work / "source"
    src.mkdir(parents=True)
    for rel in closure:
        require(inventory[rel]["sha256"] == sha(source_root / rel), f"pinned closure file changed: {rel}")
        (src / rel).parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(source_root / rel, src / rel)
    patched = set()
    for patch in spec["closure_patches"]:
        text_p = (V / patch).read_text()
        touched = re.findall(r"^\+\+\+ b/(\S+)", text_p, re.M)
        require(all(t in closure for t in touched), f"patch touches a file outside the closure: {patch}")
        require(source_file not in touched, "the module itself must not be patched")
        subprocess.run(["patch", "-s", "-p1", "-i", str(V / patch)], cwd=src, check=True)
        patched |= set(touched)
    for rel in closure:
        require((sha(src / rel) == sha(source_root / rel)) == (rel not in patched),
                f"closure file differs from the pinned file without a recorded patch: {rel}")
    vo = {}
    build_log = work / "closure_build.log"
    with build_log.open("w") as log:
        for rel in closure:
            res = subprocess.run(["zsh", "-c", 'ulimit -s 65520 && exec opam exec --switch=rocq93rc1 -- rocq c -R "$0" '
                                  'prosa "$1"', str(src), rel], cwd=src, capture_output=True, text=True)
            log.write(f"== {rel} rc={res.returncode}\n{res.stdout}{res.stderr}")
            require(res.returncode == 0 and "Error" not in res.stdout + res.stderr, f"closure compile failed: {rel}")
            vo[rel] = sha((src / rel).with_suffix(".vo"))
    require(sha(src / source_file) == sha(official), "module copy differs from the pinned source")

    # (4) Lean translation and axiom audit.
    production = PROJECT / spec["production"]
    lean_text = production.read_text()
    require(not re.search(r"\b(sorry|admit|axiom|unsafe)\b", lean_text), "forbidden Lean escape")
    lean_code = re.sub(r"--[^\n]*", "", re.sub(r"/-.*?-/", "", lean_text, flags=re.S))
    decls = re.findall(r"^\s*(?:@\[[^\]]*\]\s*)?(def|theorem|lemma|instance|abbrev|structure|class|inductive|axiom|"
                       r"example)\s+(\S+)", lean_code, re.M)
    names = [f"goal_{i}" for i in range(1, spec["goal_count"] + 1)]
    require(decls == [("theorem", n) for n in names], f"Lean declarations differ from goal_1..goal_n: {decls}")
    olean = work / "olean"
    olean.mkdir()
    for item in spec["olean_sources"]:   # accepted runs, merged in order; a later run only adds missing files
        base = V / ".work/experiments" / item / "olean"
        for f in base.rglob("*.olean"):
            dest = olean / f.relative_to(base)
            if not dest.exists():
                dest.parent.mkdir(parents=True, exist_ok=True)
                shutil.copy2(f, dest)
    dep_oleans = {}
    for stem, rel in spec["dependency_olean"].items():
        require(sha(olean / rel) == manifest_olean(stem), f"dependency olean changed: {rel}")
        dep_oleans[rel] = sha(olean / rel)
    env = dict(os.environ)
    env["LEAN_PATH"] = ":".join([str(olean)] + [str(PROJECT / f".lake/packages/{p}/.lake/build/lib/lean")
                                                for p in PACKAGES])
    env["ELAN_TOOLCHAIN"] = "leanprover/lean4:v4.33.1"
    prod_olean = olean / spec["production_olean"]
    prod_olean.parent.mkdir(parents=True, exist_ok=True)
    res = subprocess.run(["lean", "-DautoImplicit=false", "-R", str(PROJECT), "-o", str(prod_olean),
                          spec["production"]], cwd=PROJECT, env=env, capture_output=True, text=True)
    (work / "lean_build.log").write_text(res.stdout + res.stderr)
    require(res.returncode == 0 and "error" not in (res.stdout + res.stderr).lower(), "Lean build failed")
    module = spec["production"][:-len(".lean")].replace("/", ".")
    audit = work / "LeanAxiomAudit.lean"
    audit.write_text(f"import {module}\n" + "".join(f"#print axioms {spec['lean_namespace']}.{n}\n" for n in names))
    res = subprocess.run(["lean", str(audit)], cwd=PROJECT, env=env, capture_output=True, text=True)
    log = res.stdout + res.stderr
    (work / "lean_axiom_audit.log").write_text(log)
    require(res.returncode == 0 and "error" not in log.lower(), "Lean axiom audit failed to run")
    axioms = {}
    for n in names:
        m = re.search(rf"'{re.escape(spec['lean_namespace'] + '.' + n)}' (does not depend on any axioms|depends on "
                      rf"axioms: \[(.*?)\])", log, re.S)
        require(m is not None, f"no axiom report for {n}")
        found = [a.strip() for a in (m.group(2) or "").split(",") if a.strip()]
        require(set(found) <= ALLOWED_AXIOMS, f"unexpected axioms in {n}: {found}")
        axioms[n] = found

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
        "source_commit": PIN, "source_file_sha256": sha(official), "public_declaration_count": 0,
        "acceptance_mode": "GOAL_ONLY_EXAMPLE (user-authorized 2026-10-01)",
        "goal_count": spec["goal_count"],
        "official_proof_closure": {
            "files": closure, "closure_list_sha256": sha(V / spec["closure_files"]),
            "patches": {p: sha(V / p) for p in spec["closure_patches"]},
            "patched_files": sorted(patched), "vo_sha256": vo},
        "official_source_vo_sha256": vo[source_file],
        "production_file": spec["production"], "production_source_sha256": sha(production),
        "production_olean_sha256": sha(prod_olean), "dependency_olean_sha256": dep_oleans,
        "lean_goal_theorems": {n: {"axioms": axioms[n]} for n in names},
        "file_dependencies": dependency_evidence,
        "cross_itp_declaration_validation": {
            "applicability": "NOT_APPLICABLE_NO_NAMED_SOURCE_DECLARATIONS",
            "semantic_certificates": 0,
            "reason": ("The authoritative module declares no named object; its anonymous goals are checked by "
                       "compiling the byte-identical module on the verified official proof closure, and their Lean "
                       "translations by compilation and the axiom audit.")},
        "notes": spec.get("notes", ""),
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
            "goal_only_module_audited": True, "direct_dependencies_accepted": len(deps),
            "status": "ACCEPTED_V06_FILE",
            "reason": ("goal-only example module; byte-identical official module compiled on the verified official "
                       "proof closure, Lean goal theorems compiled with a clean axiom audit"),
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
    for p in ((src / source_file).with_suffix(".vo"), build_log, work / "lean_build.log",
              work / "lean_axiom_audit.log"):
        shutil.copy2(p, dest / p.name)
    print(json.dumps({"manifest": str(manifest_path), "coverage": status["coverage"]}, indent=2))


if __name__ == "__main__":
    main()
