#!/usr/bin/env python3
"""Fail-closed validation and publication of a zero-declaration classic file.

Classic-family counterpart of validate_zero_declaration_aggregation.py (which stays pinned to
v0.6).  A classic file with no named declaration (Ltac-only, Require-only, or a Require Export
aggregator) is accepted when

  1. the pinned ProsaBuddy checkout (commit, tree, clean) and the file inventory hash match, the
     declaration inventory and the evidence summary list zero declarations for it;
  2. its comment-stripped content consists only of the recorded sentences: external
     `From mathcomp|Stdlib Require ...`, `Require Import|Export prosa.*` (in the recorded order),
     and `Ltac <name> := ...` (exactly the recorded names);
  3. every file-DAG dependency is accepted (classic or v0.6 chain), and the Lean module imports
     exactly the production modules of the required prosa dependencies (read from their accepted
     manifests), in source order, and declares nothing;
  4. the byte-identical source compiles under rocq93rc1 on its recorded official closure (with the
     recorded Rocq 9.0 compatibility prelude) and a fresh `Print Module` lists no item;
  5. the Lean module compiles on hash-checked dependency oleans (each equal to its accepted
     manifest) and a compiled probe reads 0 constants of the module from the Lean environment.

Usage: validate_classic_zero_declaration.py <spec.json>
"""

from __future__ import annotations

import csv
import json
import re
import shutil
import sys
import time
from datetime import datetime, timezone
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import translation_file_pipeline as P  # noqa: E402

EXTERNAL_LIBS = {"mathcomp", "Stdlib"}


class ZeroSpec(P.Spec):
    def __init__(self, path: Path):
        self.path = path
        self.d = P.read(path)
        self.tag, self.slug, self.source = self.d["tag"], self.d["slug"], self.d["source"]
        self.work = P.EXP / f"{self.slug}_final"
        self.cert_dir = None
        self.fixtures = "Validation/fixtures/translation_order"


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


def sentences(text: str) -> list[str]:
    """Vernacular sentences: a `.` followed by whitespace or the end terminates a sentence."""
    parts = re.split(r"\.(?=\s|$)", strip_comments(text))
    return [" ".join(p.split()) for p in parts if p.strip()]


def classify(text: str, tag: str) -> dict:
    requires, ltacs, external = [], [], []
    for s in sentences(text):
        if (m := re.fullmatch(r"From (\w+) Require (Import|Export) ([\w. ]+)", s)):
            P.require(m.group(1) in EXTERNAL_LIBS, f"unexpected library: {s}", tag)
            external.append(s)
        elif (m := re.fullmatch(r"Require (Import|Export) ((?:prosa\.[\w.]+ ?)+)", s)):
            requires += [{"kind": m.group(1), "module": x} for x in m.group(2).split()]
        elif (m := re.fullmatch(r"Ltac (\w+) :=.*", s, re.S)):
            ltacs.append(m.group(1))
        else:
            raise P.Rejected(f"{tag}_REJECTED: sentence outside the zero-declaration grammar: {s[:120]}")
    return {"requires": requires, "ltac": ltacs, "external": external}


def main() -> None:
    spec = ZeroSpec(Path(sys.argv[1]).resolve())
    P.require(spec.get("family") == "classic", "classic spec required", spec.tag)
    P.configure_family(spec)
    tag, work, source = spec.tag, spec.work, spec.source
    official = P.SOURCE_ROOT / source
    P.require(P.git(P.SOURCE_ROOT, "rev-parse", "HEAD") == P.PIN, "source commit changed", tag)
    P.require(P.git(P.SOURCE_ROOT, "rev-parse", "HEAD^{tree}") == P.TREE, "source tree changed", tag)
    P.require(not P.git(P.SOURCE_ROOT, "status", "--porcelain", "--untracked-files=all"), "pinned source dirty", tag)
    with (P.DEP / "file_inventory.csv").open() as stream:
        row = next(r for r in csv.DictReader(stream) if r["file"] == source)
    P.require(row["sha256"] == P.sha(official), "file inventory mismatch", tag)
    P.require(not P.inventory(spec), "declaration inventory lists declarations", tag)
    summary = P.read(P.DEP / "generation_summary.json")
    P.require(summary["declarations_per_file"].get(source) == 0, "evidence summary does not list 0", tag)
    dag = P.read(P.DEP / "file_dag.json")
    deps = {e["dependency_file"] for e in dag["edges"] if e["dependent_file"] == source}
    P.require(deps == set(spec["dependencies"]), f"file DAG changed: {sorted(deps)}", tag)
    dependency_evidence = {d: P.accepted_status(d) for d in sorted(deps)}

    # ---- source grammar
    items = classify(official.read_text(), tag)
    P.require(items["ltac"] == spec["ltac"], f"Ltac names differ: {items['ltac']}", tag)
    P.require(items["requires"] == spec["requires"], f"prosa requires differ: {items['requires']}", tag)
    required_files = [r["module"][len("prosa."):].replace(".", "/") + ".v" for r in items["requires"]]
    P.require(set(required_files) == deps, "prosa requires differ from the file-DAG dependencies", tag)

    # ---- Lean module: imports = accepted production modules of the requires, no declaration
    def dep_manifest(f: str) -> tuple[Path, dict]:
        # the manifest paired with the status file that accepted f (classic chain first, then v0.6)
        status = P.accepted_status(f)
        status_path = (P.PIPE.parent / status) if "/" in status else (P.PIPE / status)
        path = status_path.with_name(status_path.name[:-len("status.json")] + "manifest.json")
        man = P.read(path)
        P.require(man.get("source_file") == f and man.get("acceptance") in ("ACCEPTED_CLASSIC_FILE", "ACCEPTED_V06_FILE")
                  and man.get("production_file"), f"no accepted single-file manifest for {f}", tag)
        return path, man
    expected_imports = [dep_manifest(f)[1]["production_file"][:-5].replace("/", ".") for f in required_files]
    production = P.PROJECT / spec["production"]
    lean_text = production.read_text()
    imports = re.findall(r"^import (\S+)$", lean_text, re.M)
    P.require(imports == expected_imports, f"Lean imports differ: {imports} != {expected_imports}", tag)
    lean_code = re.sub(r"--[^\n]*", "", re.sub(r"/-.*?-/", "", lean_text, flags=re.S))
    P.require([l for l in lean_code.splitlines() if l.strip() and not l.startswith("import ")] == [],
              "Lean module has content besides its imports and comments", tag)
    P.require(not P.ESCAPE_LEAN.search(lean_code), "forbidden Lean escape", tag)

    P.require(not work.exists(), f"{work} exists", tag)
    work.mkdir(parents=True)
    (work / "stage_timing.tsv").write_text("")
    t0 = time.time()

    # ---- Rocq: official closure (byte-identical module) + fresh Print Module
    (work / "compat").mkdir()
    shutil.copy2(P.CLASSIC["prelude_source"], work / "compat/Rocq90Compat.v")
    P.require(P.rocq(["Rocq90Compat.v"], work / "compat/build.log", work / "compat") == 0,
              "compatibility prelude compile failed", tag)
    src = work / "source"
    src.mkdir()
    P.build_official_closure(spec, src, work / "source_build.log")
    P.require(P.sha(src / source) == P.sha(official), "compiled module is not byte-identical", tag)
    source_vo = (src / source).with_suffix(".vo")
    module = "prosa." + source[:-2].replace("/", ".")
    probe = src / "ZeroDeclarationProbe.v"
    probe.write_text(f"Require {module}.\nPrint Module {module}.\n")
    P.require(P.rocq(["-R", str(src), "prosa", probe.name], work / "print_module.log", src) == 0,
              "Print Module probe failed", tag)
    printed = " ".join((work / "print_module.log").read_text().split())
    short = source[:-2].rsplit("/", 1)[-1]
    P.require(re.search(rf"Module {re.escape(short)} := Struct End", printed) is not None,
              f"Print Module lists items: {printed[-400:]}", tag)
    P.stamp(spec, "rocq_source", time.time() - t0)
    t0 = time.time()

    # ---- Lean: hash-checked dependency oleans + module + zero-constant probe
    olean = work / "olean"
    olean.mkdir()
    olean_evidence = {}
    # every Prosa dependency olean of the module (transitively), copied from an accepted run and bound to the
    # manifest that accepted it (classic: production_olean_sha256; v0.6: the accepting manifest's olean hash)
    import classic_mkfile as M
    for art in M.auto_olean_artifacts([spec["production"][:-5].replace("/", ".")]):
        dest = olean / art["to"]
        dest.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(P.EXP / art["from"], dest)
        P.require(P.sha(dest) == P.extra_olean_hash(art), f"dependency olean changed: {art['to']}", tag)
        olean_evidence[art["to"]] = {k: art[k] for k in ("v06_file", "manifest") if k in art} | {"sha256": P.sha(dest)}
    for f in required_files:
        path, man = dep_manifest(f)
        rel = man["production_file"][:-5] + ".olean"
        P.require((olean / rel).is_file() and P.sha(olean / rel) == man["production_olean_sha256"],
                  f"dependency olean differs from its manifest: {rel}", tag)
        olean_evidence[rel]["direct_dependency"] = f
    env = P.lean_env(olean)
    prod_out = olean / spec["production_olean"]
    prod_out.parent.mkdir(parents=True, exist_ok=True)
    P.require(P.run(["lean", *P.LEAN_OPTIONS, "-o", str(prod_out), spec["production"]],
                    work / "lean_build.log", P.PROJECT, env) == 0, "Lean module build failed", tag)
    lean_module = spec["production"][:-5].replace("/", ".")
    lprobe = work / "ZeroDeclarationProbe.lean"
    lprobe.write_text(
        f"import {lean_module}\nimport Lean\nopen Lean in\n#eval show CoreM Unit from do\n"
        f"  let env ← getEnv\n"
        f"  let some idx := env.getModuleIdx? `{lean_module} | throwError \"module missing\"\n"
        f"  IO.println s!\"ZERO_DECLARATION_PROBE {{(env.header.moduleData[idx.toNat]!).constNames.size}}\"\n")
    P.require(P.run(["lean", *P.LEAN_OPTIONS, str(lprobe)], work / "lean_probe.log", P.PROJECT, env) == 0,
              "Lean probe failed", tag)
    P.require("ZERO_DECLARATION_PROBE 0" in (work / "lean_probe.log").read_text().split("\n"),
              "Lean module declares constants", tag)
    P.stamp(spec, "lean_module", time.time() - t0)

    # ---- publication (classic status chain)
    previous_path = P.PIPE / spec["previous_status"]
    previous = P.read(previous_path)
    P.require(previous["status"] == "PASS"
              and previous["coverage"]["accepted_files"] == spec["previous_files"]
              and previous["coverage"]["accepted_declarations"] == spec["previous_decls"],
              "formal baseline changed", tag)
    if (P.ROOT / "Prosa-fei").exists():
        P.require(not P.git(P.ROOT, "status", "--porcelain", "--", "Prosa-fei"), "Prosa-fei changed", tag)
    now = datetime.now(timezone.utc).astimezone()
    timing = [l.split("\t") for l in (work / "stage_timing.tsv").read_text().splitlines()]
    manifest = {
        "slice": P.SLICE_PREFIX + spec.slug.upper(),
        "generated_at": now.isoformat(), "published_at": now.isoformat(),
        "rank": spec["rank"], "layer": spec["layer"], "source_file": source,
        "source_commit": P.PIN, "source_tree": P.TREE, "source_file_sha256": P.sha(official),
        "pipeline": "Validation/scripts/validate_classic_zero_declaration.py",
        "spec": str(spec.path.relative_to(P.PROJECT)), "spec_sha256": P.sha(spec.path),
        "public_declaration_count": 0,
        "source_content": {"ltac": items["ltac"], "requires": items["requires"], "external": items["external"]},
        "source_compatibility": {
            "mode": "official_closure", "closure_list_sha256": P.sha(P.V / spec["official_closure"]["files"]),
            "classic_prelude": {"file": str(P.CLASSIC["prelude_source"].relative_to(P.PROJECT)),
                                "sha256": P.CLASSIC["prelude_sha256"],
                                "vo_sha256": P.sha(work / "compat/Rocq90Compat.vo")}},
        "print_module_sha256": P.sha(work / "print_module.log"),
        "file_dependencies": dependency_evidence,
        "dependency_oleans": olean_evidence,
        "production_file": spec["production"], "production_source_sha256": P.sha(production),
        "production_olean_sha256": P.sha(prod_out),
        "lean_probe_sha256": P.sha(lprobe), "source_vo_sha256": P.sha(source_vo),
        "stage_timing_seconds": {s: {"mode": m, "seconds": int(t)} for s, m, t in timing},
        "cross_itp_declaration_validation": {
            "applicability": "NOT_APPLICABLE_NO_NAMED_SOURCE_DECLARATIONS",
            "lean4export_executions": 0, "rocq_import_executions": 0, "semantic_certificates": 0,
            "reason": ("The authoritative module declares no named object (fresh Print Module is empty). "
                       "Its content (Ltac tactics / Require lists) is validated by an exact sentence grammar, "
                       "the byte-identical compiled Rocq module, accepted hash-bound dependencies, and a compiled "
                       "Lean module whose environment holds 0 constants of its own.")},
        "notes": spec.get("notes", ""),
        "acceptance": P.ACCEPT_FILE,
    }
    manifest_path = P.PIPE / f"{spec.slug}_module_manifest.json"
    status_path = P.PIPE / f"{spec.slug}_module_status.json"
    P.require(not manifest_path.exists() and not status_path.exists(), "publication already exists", tag)
    destination = P.PUBLISH_DIR / spec.slug
    P.require(not destination.exists(), "publication destination exists", tag)
    manifest_path.write_text(json.dumps(manifest, indent=2) + "\n")
    status = {
        "slice": manifest["slice"], "status": "PASS", "source_file": source,
        "per_file": {source: {
            "public_declarations": 0, "translated": 0, "proof_clean": 0, "certified": 0,
            "module_interface_audited": True, "direct_dependencies_accepted": len(deps),
            "status": P.ACCEPT_FILE,
            "reason": "zero-declaration classic file; exact sentence grammar, accepted dependency/hash closure, "
                      "official Rocq compile with empty Print Module, and compiled Lean module with 0 constants",
            "published_at": now.isoformat()}},
        "coverage": {
            "accepted_files": spec["previous_files"] + 1, "authoritative_files": P.AUTHORITATIVE["files"],
            "accepted_declarations": spec["previous_decls"],
            "authoritative_declarations": P.AUTHORITATIVE["declarations"],
            "translated_but_not_certified": previous["coverage"]["translated_but_not_certified"],
            "deferred_external_boundary": previous["coverage"]["deferred_external_boundary"]},
        "previous_status_sha256": P.sha(previous_path), "manifest_sha256": P.sha(manifest_path),
    }
    status_path.write_text(json.dumps(status, indent=2) + "\n")
    destination.mkdir(parents=True)
    for p in (source_vo, work / "source_build.log", work / "print_module.log", work / "lean_build.log",
              work / "lean_probe.log", lprobe, work / "stage_timing.tsv"):
        shutil.copy2(p, destination / p.name)
    print(json.dumps({"manifest": str(manifest_path), "coverage": status["coverage"]}, indent=2))


if __name__ == "__main__":
    main()
