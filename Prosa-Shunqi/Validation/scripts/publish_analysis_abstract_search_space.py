#!/usr/bin/env python3
"""Fail-closed, serialized publication of Rank 63 SearchSpace revalidation."""

from __future__ import annotations

import csv
import hashlib
import json
import re
import shutil
import subprocess
import tempfile
from datetime import datetime, timedelta, timezone
from pathlib import Path


PROJECT = Path(__file__).resolve().parents[2]
ROOT = PROJECT.parent
V = PROJECT / "Validation"
PIPE = V / "planning/v06_pipeline"
W = V / ".work/experiments/analysis_abstract_search_space"
PIN = "414e66760333eaa4ef78c685bcf53291c527a548"
TREE = "7d7e94c731f7eefde4ca738310d4cafdd7bebdf0"
SOURCE = "analysis/abstract/search_space.v"
NAMES = (
    "are_equivalent_at_values_less_than",
    "are_not_equivalent_at_values_less_than",
    "is_in_search_space",
    "representative_exists",
    "solution_for_A_exists",
    "search_space_switch_IBF",
)
THEOREMS = NAMES[3:]
FOUNDATIONS = ("PropSPropFoundation", "LogicalRelation", "SubadditivityNatCorrespondence")
CERTIFICATES = (
    "SearchSpaceBaseAdapter", "SearchSpaceLogicalOperations",
    "SearchSpaceDefinitionsCorrespondence",
    "SearchSpaceRepresentativeCorrespondence",
    "SearchSpaceSolutionCorrespondence", "SearchSpaceSwitchCorrespondence",
    "SearchSpaceExactTypeGuards", "SearchSpaceAssumptionAudit",
)


def require(value: bool, reason: str) -> None:
    if not value:
        raise SystemExit("SEARCH_SPACE_PUBLICATION_REJECTED: " + reason)


def sha(path: Path) -> str:
    require(path.is_file() and path.stat().st_size > 0, f"missing/empty: {path}")
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read(path: Path) -> dict:
    require(path.is_file(), f"missing: {path}")
    return json.loads(path.read_text())


def command(*args: str) -> str:
    return subprocess.check_output(args, text=True).strip()


def latest_status() -> tuple[Path, dict]:
    candidates = []
    for path in PIPE.glob("*_module_status.json"):
        status = read(path)
        if status.get("status") == "PASS":
            coverage = status.get("coverage", {})
            candidates.append((coverage.get("accepted_files", -1),
                               coverage.get("accepted_declarations", -1), path))
    require(bool(candidates), "no formal cumulative status")
    latest = max(candidates)
    require(sum(item[:2] == latest[:2] for item in candidates) == 1,
            "ambiguous cumulative status")
    require(latest[0] >= 62 and latest[1] >= 448,
            "Rank 65 accepted baseline missing")
    return latest[2], read(latest[2])


def accepted_manifest_corpus() -> list[str]:
    corpus = []
    legacy = {
        "foundation_slice_1_manifest.json": "FOUNDATION_SLICE_1_STATUS",
        "foundation_slice_2_closure_manifest.json": "FOUNDATION_SLICE_2_CLOSURE_STATUS",
        "utility_foundation_expansion_manifest.json": "UTILITY_FOUNDATION_EXPANSION_STATUS",
    }
    for path in PIPE.glob("*manifest.json"):
        status_path = path.with_name(path.name.replace("manifest.json", "status.json"))
        if not status_path.is_file():
            continue
        status = read(status_path)
        manifest = read(path)
        if ((manifest.get("acceptance") == "ACCEPTED_V06_FILE"
             and status.get("status") == "PASS")
                or (path.name in legacy
                    and status.get(legacy[path.name]) == "PASS")):
            corpus.append(path.read_text())
    require(len(corpus) >= 50, "accepted dependency manifest corpus incomplete")
    return corpus


def main() -> None:
    previous_path, previous = latest_status()
    official_root = V / ".work/prosa-v06-414e667"
    official = official_root / SOURCE
    patched = W / "source" / SOURCE
    source_vo = patched.with_suffix(".vo")
    patch = V / "patches/prosa-v06-rocq93-analysis-abstract-search-space.patch"
    require(command("git", "-C", str(official_root), "rev-parse", "HEAD") == PIN
            and command("git", "-C", str(official_root), "rev-parse", "HEAD^{tree}") == TREE
            and not command("git", "-C", str(official_root), "status", "--porcelain",
                            "--untracked-files=all"),
            "pinned official source not exact/clean")
    require(sha(official) == "03e226ba30583624241d1de169c4fe28244b8fb6c0f06412ed1585a4fe2747bc"
            and sha(patched) == "3d5b337adcb75eb89ff5f3bde3ae4b1b0af4ffb5ed05c29039a8e0fd79f7bc17"
            and sha(patch) == "3f807c16a75643ca5feeb86b55b55a41b676dfc81b65dc2f993e665296425108"
            and source_vo.stat().st_mtime_ns > patched.stat().st_mtime_ns,
            "source/compatibility patch or Rocq source build changed")
    with (V / "planning/v06_dependency/file_inventory.csv").open() as stream:
        inventory_row = next(row for row in csv.DictReader(stream)
                             if row["file"] == SOURCE)
    require(inventory_row["sha256"] == sha(official)
            and inventory_row["layer"] == "11", "authoritative file inventory changed")
    with (V / "planning/v06_dependency/declaration_inventory.csv").open() as stream:
        rows = [row for row in csv.DictReader(stream) if row["source_file"] == SOURCE]
    types = read(V / "planning/v06_dependency/declaration_type_evidence.json")
    require([row["declaration_name"] for row in rows] == list(NAMES)
            and [row["kind"] for row in rows] == ["Definition"] * 3 + ["Lemma"] * 3
            and all(row["final_type_or_type_fingerprint"] ==
                    "rocq-check-sha256:" + types[row["qualified_name"]]["sha256"]
                    for row in rows), "public declarations/elaborated types changed")
    graph = read(V / "planning/v06_dependency/file_dag.json")
    deps = {edge["dependency_file"] for edge in graph["edges"]
            if edge["dependent_file"] == SOURCE}
    require(deps == {"model/task/concept.v", "util/epsilon.v", "util/tactics.v"},
            "file DAG changed")
    for dep in deps:
        require(dep in previous.get("per_file", {})
                or any(dep in text for text in accepted_manifest_corpus()),
                f"dependency not accepted: {dep}")

    require("Lean (version 4.33.1" in command("lean", "--version")
            and command("git", "-C", str(PROJECT / ".lake/packages/mathlib"),
                        "rev-parse", "HEAD") ==
            "0df444a360eaa60ab8c11dca51a86af692955474"
            and "9.3" in command("opam", "exec", "--switch=rocq93rc1",
                                 "--", "rocq", "--version"),
            "toolchain changed")
    tooling = read(V / "tooling/tooling_manifest.json")
    require(sha(V / ".work/tooling/lean4export/.lake/build/bin/lean4export")
            == tooling["lean4export"]["expected_binary_sha256"]
            and sha(V / ".work/tooling/rocq-lean-import/src/lean_import.cmxs")
            == tooling["rocq_lean_import"]["expected_plugin_sha256"]
            and sha(V / ".work/tooling/rocq-lean-import/src/Lean.vo")
            == tooling["rocq_lean_import"]["expected_foundation_vo_sha256"],
            "export/import tooling changed")

    production = PROJECT / "Prosa/Analysis/Abstract/SearchSpace.lean"
    olean_root = W / "olean"
    olean = olean_root / "Prosa/Analysis/Abstract/SearchSpace.olean"
    lean_audit_source = V / "fixtures/translation_order/SearchSpaceLeanTypeAudit.lean"
    lean_audit_olean = olean_root / "Validation/fixtures/translation_order/SearchSpaceLeanTypeAudit.olean"
    for source, artifact in ((production, olean), (lean_audit_source, lean_audit_olean)):
        require(sha(source) and sha(artifact)
                and artifact.stat().st_mtime_ns > source.stat().st_mtime_ns
                and not re.search(r"\b(sorry|axiom|unsafe)\b", source.read_text()),
                f"Lean source or fresh build invalid: {source}")
    require(sha(production) == "8bff043617fc6f4f29c241fb80e2e16e0d9744258cf7b2746b803972f31ac9db"
            and sha(olean) == "f9b71872a48c0b9c764522a79dc0fb1327f20b0a56a07565e2ad311e35e2b9b8",
            "merged compiled Lean snapshot differs from frozen handoff")
    corpus = accepted_manifest_corpus()
    dependency_count = 0
    for artifact in (olean_root / "Prosa").rglob("*.olean"):
        rel = artifact.relative_to(olean_root)
        if rel.parts[:2] == ("Prosa", "Prosa") or artifact == olean:
            continue  # An unused generated-copy path is not on LEAN_PATH as a module.
        dep_source = PROJECT / rel.with_suffix(".lean")
        require(any(sha(artifact) in text and sha(dep_source) in text for text in corpus),
                f"unverified accepted dependency/source pair: {rel}")
        dependency_count += 1
    require(dependency_count == 33, "compiled dependency closure changed")
    lean_log = (W / "lean_axiom_audit.log").read_text()
    require("error:" not in lean_log.lower() and "sorryAx" not in lean_log,
            "Lean audit has errors or sorryAx")
    allowed_axioms = {"propext", "Classical.choice", "Quot.sound"}
    for name in THEOREMS:
        match = re.search(r"'Prosa\.Analysis\.Abstract\.SearchSpace\." + name +
                          r"' depends on axioms: \[([^\]]*)\]", lean_log)
        clean = ("'Prosa.Analysis.Abstract.SearchSpace." + name +
                 "' does not depend on any axioms") in lean_log
        require(bool(match) or clean, f"Lean axiom output missing: {name}")
        if match:
            require(set(match.group(1).split(", ")) <= allowed_axioms,
                    f"unexpected Lean axiom: {name}")

    export_config = V / "tooling/analysis_abstract_search_space_export_config.json"
    config = read(export_config)
    exported = W / "imported/SearchSpaceFull.out"
    imported_v = W / "imported/ImportedSearchSpace.v"
    imported_vo = W / "imported/ImportedSearchSpace.vo"
    require(config["targets"] == ["Prosa.Analysis.Abstract.SearchSpace." + name
                                  for name in NAMES]
            and config["statement_only"] == []
            and config["body_theorems"] == ["Prosa.Analysis.Abstract.SearchSpace." + name
                                           for name in THEOREMS]
            and sha(exported) == "d448ee305e0de2af9c80341cad831ba47d376902c3552af075c66d771778fb69"
            and sha(imported_v) and sha(imported_vo)
            and imported_vo.stat().st_mtime_ns > exported.stat().st_mtime_ns
            and "Error:" not in (W / "export.log").read_text()
            and "Error:" not in (W / "import.log").read_text(),
            "actual full-body export/import invalid")
    source_audit = V / "fixtures/translation_order/SearchSpaceSourceTypeAudit.v"
    require(sha(source_audit) and "Closed under the global context" in
            (W / "source_type_audit.log").read_text(),
            "official elaborated source theorem type probe missing")
    cert_dir = W / "certificates"
    controlled = V / "certificates/analysis_abstract_search_space"
    for name in FOUNDATIONS + CERTIFICATES:
        source = controlled / f"{name}.v"
        if name in FOUNDATIONS:
            source = V / "certificates/common" / f"{name}.v"
        proof = cert_dir / f"{name}.v"
        vo = cert_dir / f"{name}.vo"
        body = proof.read_text()
        require(sha(source) == sha(proof) and sha(vo)
                and vo.stat().st_mtime_ns > proof.stat().st_mtime_ns
                and vo.stat().st_mtime_ns > imported_vo.stat().st_mtime_ns
                and "Error:" not in (W / f"{name}.log").read_text(),
                f"controlled certificate not rebuilt: {name}")
        if name == "PropSPropFoundation":
            require(len(re.findall(r"\bAxiom\b", body)) == 1
                    and "Axiom interpret_strict :" in body,
                    "Prop/SProp foundation changed")
        else:
            require(not re.search(r"\b(Axiom|Admitted|admit|sorry)\b", body),
                    f"forbidden proof gap: {name}")
    audit = read(W / "assumption_audit.json")
    require(audit["audit_policy"] == "fail_closed"
            and set(audit["certificates"]) == set(NAMES)
            and "AUDIT_END search_space_switch_IBF" in
            (W / "SearchSpaceAssumptionAudit.log").read_text(),
            "assumption log missing/truncated")
    for name in NAMES:
        entry = audit["certificates"][name]
        require(entry["status"] == "CERTIFIED_WITH_PROP_SPROP_FOUNDATION"
                and entry["semantic_premises"] == []
                and entry["statement_only_dependencies"] == []
                and entry["unexpected"] == []
                and entry["prop_sprop_foundation"] ==
                ["PropSPropFoundation.interpret_strict"]
                and not entry["source_theorem_dependency"]
                and not entry["target_theorem_dependency"],
                f"fail-closed semantic audit rejected {name}")
    require(not command("git", "-C", str(ROOT), "status", "--porcelain", "--",
                        "Prosa-fei"), "historical workspace changed")
    subprocess.run(["git", "-C", str(ROOT), "diff", "--check"], check=True)

    destination = V / "imported/translation_order/analysis_abstract_search_space"
    manifest_path = PIPE / "analysis_abstract_search_space_module_manifest.json"
    status_path = PIPE / "analysis_abstract_search_space_module_status.json"
    require(not destination.exists() and not manifest_path.exists()
            and not status_path.exists(), "SearchSpace already published")
    destination.parent.mkdir(parents=True, exist_ok=True)
    stage = Path(tempfile.mkdtemp(prefix=".search-space-", dir=destination.parent))
    artifacts = {
        "official_source": official, "patched_source": patched,
        "compatibility_patch": patch, "source_vo": source_vo,
        "production_source": production, "production_olean": olean,
        "lean_type_audit_source": lean_audit_source,
        "lean_type_audit_olean": lean_audit_olean,
        "lean_axiom_audit_log": W / "lean_axiom_audit.log",
        "source_type_audit_source": source_audit,
        "source_type_audit_log": W / "source_type_audit.log",
        "export_config": export_config, "export": exported,
        "imported_v": imported_v, "imported_vo": imported_vo,
        "assumption_config": controlled / "search_space_assumption_config.json",
        "assumption_summary": W / "assumption_audit.json",
        "assumption_log": W / "SearchSpaceAssumptionAudit.log",
    }
    for key in ("patched_source", "source_vo", "lean_axiom_audit_log",
                "source_type_audit_log", "export", "imported_v", "imported_vo",
                "assumption_summary", "assumption_log"):
        source = artifacts[key]
        name = key + source.suffix
        shutil.copy2(source, stage / name)
        artifacts[key] = stage / name
    (stage / "certificates").mkdir()
    for name in FOUNDATIONS + CERTIFICATES:
        for suffix in (".v", ".vo"):
            source = cert_dir / f"{name}{suffix}"
            target = stage / "certificates" / source.name
            shutil.copy2(source, target)
            artifacts[f"{name}{suffix}"] = target
    require(sha(stage / "imported_vo.vo") == sha(imported_vo)
            and sha(stage / "export.out") == sha(exported),
            "publication stage copy corrupted")
    stage.rename(destination)
    artifacts = {key: destination / path.relative_to(stage)
                 if path.is_relative_to(stage) else path
                 for key, path in artifacts.items()}
    declarations = []
    for row in rows:
        name = row["declaration_name"]
        entry = audit["certificates"][name]
        declarations.append({
            "source_declaration": row["qualified_name"],
            "lean_declaration": "Prosa.Analysis.Abstract.SearchSpace." + name,
            "kind": row["kind"],
            "source_command_sha256": row["source_command_sha256"],
            "source_elaborated_type_sha256": types[row["qualified_name"]]["sha256"],
            "semantic_certificate": entry["certificate"],
            "semantic_status": entry["status"],
            "semantic_premises": [], "statement_only_dependencies": [],
            "source_theorem_dependency": False, "target_theorem_dependency": False,
            "unexpected_assumptions": [],
            "prop_sprop_foundation": ["PropSPropFoundation.interpret_strict"],
            "acceptance": "ACCEPTED_V06_TRANSLATION",
        })
    manifest = {
        "slice": "ANALYSIS_ABSTRACT_SEARCH_SPACE", "source_commit": PIN,
        "source_file": SOURCE, "source_file_sha256": sha(official),
        "source_acquisition": {"mode": "FRESH",
                               "proof_only_compat_patch_sha256": sha(patch)},
        "direct_file_dependencies": sorted(deps),
        "accepted_compiled_dependency_oleans": dependency_count,
        "production_file": str(production.relative_to(PROJECT)),
        "production_source_sha256": sha(production),
        "production_olean_sha256": sha(olean),
        "validation_mode": "FILE_VALIDATE_WITH_VERIFIED_ACCEPTED_PRODUCERS",
        "target_build": "FRESH", "export": "FRESH", "rocq_import": "FRESH",
        "acceptance": "ACCEPTED_V06_FILE", "declarations": declarations,
        "artifact_hashes": {key + "_sha256": sha(path) for key, path in artifacts.items()},
        "artifact_paths": {key: str(path.relative_to(PROJECT))
                           for key, path in artifacts.items()
                           if path.is_relative_to(PROJECT)},
        "tooling_manifest_sha256": sha(V / "tooling/tooling_manifest.json"),
        "previous_status_file": previous_path.name,
        "previous_status_sha256": sha(previous_path),
        "published_at": datetime.now(timezone(timedelta(hours=8))).isoformat(),
    }
    manifest_path.write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")
    coverage = {**previous["coverage"],
                "accepted_files": previous["coverage"]["accepted_files"] + 1,
                "accepted_declarations": previous["coverage"]["accepted_declarations"] + 6}
    status = {
        "slice": manifest["slice"], "status": "PASS",
        "per_file": {SOURCE: {
            "public_declarations": 6, "translated": 6, "proof_clean": 6,
            "certified": 0, "certified_with_prop_sprop_foundation": 6,
            "status": "ACCEPTED_V06_FILE",
        }},
        "coverage": coverage, "manifest_sha256": sha(manifest_path),
    }
    status_path.write_text(json.dumps(status, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"status": "PASS", "coverage": coverage}, sort_keys=True))


if __name__ == "__main__":
    main()
