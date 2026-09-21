#!/usr/bin/env python3
"""Publish one fully checked utility-file cluster as content-addressed evidence."""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
import re
import subprocess
from pathlib import Path


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def text_sha(text: str) -> str:
    return hashlib.sha256(text.encode()).hexdigest()


def digest_json(value: object) -> str:
    return hashlib.sha256(json.dumps(value, sort_keys=True).encode()).hexdigest()


def freeze_sections(text: str) -> dict[str, str]:
    result: dict[str, str] = {}
    current: str | None = None
    lines: list[str] = []
    for line in text.splitlines():
        if line.startswith("FREEZE_BEGIN "):
            if current is not None:
                raise SystemExit(f"nested/truncated freeze section: {current}")
            current = line.removeprefix("FREEZE_BEGIN ")
            lines = []
        elif line.startswith("FREEZE_END "):
            name = line.removeprefix("FREEZE_END ")
            if name != current:
                raise SystemExit(f"freeze marker mismatch: {current!r} / {name!r}")
            result[name] = "\n".join(lines).strip()
            current = None
            lines = []
        elif current is not None:
            lines.append(line)
    if current is not None:
        raise SystemExit(f"truncated freeze section: {current}")
    return result


def git(path: Path, *args: str) -> str:
    return subprocess.check_output(["git", "-C", str(path), *args], text=True).strip()


def main() -> None:
    p = argparse.ArgumentParser()
    p.add_argument("--project-root", required=True, type=Path)
    p.add_argument("--validation-root", required=True, type=Path)
    p.add_argument("--source-root", required=True, type=Path)
    p.add_argument("--exporter-root", required=True, type=Path)
    p.add_argument("--importer-root", required=True, type=Path)
    p.add_argument("--work", required=True, type=Path)
    p.add_argument("--config", required=True, type=Path)
    p.add_argument("--freeze-log", required=True, type=Path)
    p.add_argument("--lean-axioms", required=True, type=Path)
    p.add_argument("--assumptions", required=True, type=Path)
    p.add_argument("--baseline", required=True, type=Path)
    p.add_argument("--snapshot-id")
    p.add_argument("--prepare-manifest", type=Path)
    p.add_argument("--prepare-evidence", type=Path)
    p.add_argument("--output", required=True, type=Path)
    args = p.parse_args()

    project = args.project_root.resolve()
    validation = args.validation_root.resolve()
    config = json.loads(args.config.read_text())
    source_file = config["source_file"]
    validation_source_file = config.get("validation_source_file", source_file)
    source_validation_vo = config.get(
        "source_validation_vo", source_file.replace(".v", ".vo")
    )
    source_metadata_name = config.get("source_acquisition_metadata")
    stem = config["artifact_stem"]
    inventory = [
        row for row in csv.DictReader(
            (validation / "planning/v06_dependency/declaration_inventory.csv").open()
        ) if row["source_file"] == source_file
    ]
    migrations = {
        (row["v06_file"], row["v06_declaration"]): row
        for row in csv.DictReader(
            (validation / "planning/v06_mapping/v06_migration_table.csv").open()
        )
    }
    configured = config["declarations"]
    source_names = {row["declaration_name"] for row in inventory}
    partial_inventory = bool(config.get("partial_inventory", False))
    if partial_inventory:
        unknown = set(configured) - source_names
        if unknown:
            raise SystemExit(
                f"partial-cluster config has declarations absent from {source_file}: "
                f"{sorted(unknown)}"
            )
        inventory = [
            row for row in inventory if row["declaration_name"] in configured
        ]
    elif source_names != set(configured):
        raise SystemExit(
            f"whole-file config mismatch for {source_file}: "
            f"missing={sorted(source_names-set(configured))}, "
            f"extra={sorted(set(configured)-source_names)}"
        )

    freezes = freeze_sections(args.freeze_log.read_text())
    lean_audits = json.loads(args.lean_axioms.read_text())
    if lean_audits.get("missing") or lean_audits.get("extra"):
        raise SystemExit("Lean proof audit incomplete")
    assumptions = json.loads(args.assumptions.read_text())["certificates"]
    baseline = json.loads(args.baseline.read_text())
    if baseline["status"] != "PASS":
        raise SystemExit("frozen baseline was invalidated")

    prepare_manifest = None
    prepare_evidence = None
    if args.snapshot_id is not None:
        if args.prepare_manifest is None or args.prepare_evidence is None:
            raise SystemExit(
                "snapshot-aware publication requires prepare manifest and evidence"
            )
        prepare_manifest = json.loads(args.prepare_manifest.read_text())
        prepare_evidence = json.loads(args.prepare_evidence.read_text())
        if prepare_manifest.get("snapshot_id") != args.snapshot_id:
            raise SystemExit("publication prepare-manifest snapshot mismatch")
        if prepare_evidence.get("snapshot_id") != args.snapshot_id:
            raise SystemExit("publication prepare-evidence snapshot mismatch")
        required_stages = {
            "lean_build", "source_acquisition", "export", "rocq_import"
        }
        stages = prepare_evidence.get("stages", [])
        by_name = {stage.get("stage"): stage for stage in stages}
        if set(by_name) != required_stages:
            raise SystemExit("publication prepare-stage evidence incomplete")
        for name, stage in by_name.items():
            if stage.get("mode") not in {"FRESH", "VERIFIED_CACHE"}:
                raise SystemExit(f"unknown prepare evidence mode: {name}")
            if stage.get("mode") == "FRESH" and not stage.get("executed"):
                raise SystemExit(f"fresh prepare stage was not executed: {name}")
            if stage.get("mode") == "VERIFIED_CACHE" and stage.get("executed"):
                raise SystemExit(f"cache stage unexpectedly executed: {name}")

    lean_source = project / config["lean_file"]
    olean = args.work / "olean" / config["lean_file"].replace(".lean", ".olean")
    export = args.work / "imported" / f"{stem}.out"
    imported_vo = args.work / "imported" / f"Imported{stem}.vo"
    validation_source = args.work / "source" / validation_source_file
    source_vo = args.work / "source" / source_validation_vo
    source_metadata = None
    source_metadata_sha256 = None
    if source_metadata_name is not None:
        source_metadata_path = args.work / "source" / source_metadata_name
        source_metadata = json.loads(source_metadata_path.read_text())
        source_metadata_sha256 = sha(source_metadata_path)
        if source_metadata.get("source_file") != source_file:
            raise SystemExit("source acquisition metadata file mismatch")
        if source_metadata.get("source_commit") != git(args.source_root, "rev-parse", "HEAD"):
            raise SystemExit("source acquisition metadata commit mismatch")
        if source_metadata.get("source_file_sha256") != sha(args.source_root / source_file):
            raise SystemExit("source acquisition metadata hash mismatch")
        metadata_expected = set(configured) | set(
            config.get("source_acquisition_dependency_declarations", [])
        )
        metadata_actual = set(source_metadata.get("declarations", {}))
        if partial_inventory:
            missing = metadata_expected - metadata_actual
            unknown = metadata_actual - source_names
            if missing or unknown:
                raise SystemExit(
                    "source acquisition metadata declaration coverage mismatch: "
                    f"missing={sorted(missing)}, unknown={sorted(unknown)}"
                )
        elif metadata_actual != metadata_expected:
            raise SystemExit("source acquisition metadata declaration coverage mismatch")
    certificate_root = validation / "certificates/utility_foundation"
    common_root = validation / "certificates/common"
    evidence_roots = {
        "project": project,
        "validation": validation,
        "work": args.work,
    }
    additional_evidence = {}
    for label, evidence in config.get("additional_evidence", {}).items():
        base = evidence_roots.get(evidence["base"])
        if base is None:
            raise SystemExit(f"unknown additional-evidence base: {evidence['base']}")
        path = base / evidence["path"]
        if not path.is_file() or not path.stat().st_size:
            raise SystemExit(f"additional evidence absent or empty: {path}")
        additional_evidence[label] = {
            "path": str(path),
            "sha256": sha(path),
        }

    rows = []
    for row in inventory:
        name = row["declaration_name"]
        spec = configured[name]
        lean_name = config["lean_prefix"] + name
        if lean_name not in freezes:
            raise SystemExit(f"missing Lean type freeze: {lean_name}")
        audit = assumptions[spec["audit_key"]]
        lean_audit = lean_audits["declarations"].get(lean_name)
        if not lean_audit or lean_audit["status"] != "PASS":
            raise SystemExit(f"Lean proof audit failed: {lean_name}")
        accepted = audit["status"] in {
            "CERTIFIED", "CERTIFIED_WITH_PROP_SPROP_FOUNDATION"
        }
        if not accepted:
            raise SystemExit(f"semantic audit failed: {lean_name}: {audit['status']}")
        cert_source = certificate_root / spec["certificate_file"]
        if not cert_source.is_file():
            cert_source = common_root / spec["certificate_file"]
        if not cert_source.is_file():
            raise SystemExit(
                f"certificate source not found: {spec['certificate_file']}"
            )
        cert_vo = args.work / "certificates" / spec["certificate_file"].replace(".v", ".vo")
        bridge_hashes = {}
        for bridge in spec["bridge_files"]:
            path = common_root / bridge
            bridge_hashes[bridge] = sha(path)
        migration = migrations[(source_file, name)]
        invalidation_material = {
            "source_command": row["source_command_sha256"],
            "source_type": row["final_type_or_type_fingerprint"],
            "validation_source": sha(validation_source),
            "source_validation_vo": sha(source_vo),
            "source_acquisition_metadata": source_metadata_sha256,
            "lean_source": sha(lean_source),
            "lean_type": text_sha(freezes[lean_name]),
            "olean": sha(olean),
            "export": sha(export),
            "import": sha(imported_vo),
            "certificate_source": sha(cert_source),
            "certificate_vo": sha(cert_vo),
            "assumptions": audit["raw_section_sha256"],
            "bridges": bridge_hashes,
            "additional_evidence": additional_evidence,
        }
        rows.append({
            "source_file": source_file,
            "rocq_declaration": row["qualified_name"],
            "kind": row["kind"],
            "source_command_sha256": row["source_command_sha256"],
            "source_elaborated_type_fingerprint": row["final_type_or_type_fingerprint"],
            "lean_file": config["lean_file"],
            "lean_declaration": lean_name,
            "migration_action": migration["reuse_action"],
            "lean_elaborated_type": freezes[lean_name],
            "lean_type_sha256": text_sha(freezes[lean_name]),
            "lean_source_sha256": sha(lean_source),
            "fresh_olean_sha256": sha(olean),
            "export_sha256": sha(export),
            "imported_vo_sha256": sha(imported_vo),
            "source_validation_vo_sha256": sha(source_vo),
            "official_source_vo_sha256": (
                sha(source_vo) if validation_source_file == source_file else None
            ),
            "lean_proof_audit": lean_audit,
            "certificate": spec["certificate"],
            "certificate_module": spec["certificate_file"],
            "certificate_source_sha256": sha(cert_source),
            "certificate_vo_sha256": sha(cert_vo),
            "semantic_relation": spec["semantic_relation"],
            "semantic_status": audit["status"],
            "assumption_audit": audit,
            "semantic_premises": audit["semantic_premises"],
            "foundation_dependencies": {
                "prop_sprop": audit["prop_sprop_foundation"],
                "importer": audit["importer_foundation"],
                "rocq_sprop_definitional_uip": audit["rocq_sprop_definitional_uip"],
                "bridge_source_sha256": bridge_hashes,
            },
            "acceptance": "ACCEPTED_V06_TRANSLATION",
            "snapshot_id": args.snapshot_id,
            "evidence_scope": (
                "CURRENT_SNAPSHOT" if args.snapshot_id is not None
                else "LEGACY_UNTIMED"
            ),
            "content_invalidation_key_sha256": digest_json(invalidation_material),
        })

    prepare_modes = {}
    if prepare_evidence is not None:
        prepare_modes = {
            stage["stage"]: stage["mode"]
            for stage in prepare_evidence["stages"]
        }
    current_run_fresh = bool(prepare_modes) and all(
        mode == "FRESH" for mode in prepare_modes.values()
    )
    result = {
        "source_file": source_file,
        "file_status": (
            "PARTIAL_V06_FILE" if partial_inventory else "ACCEPTED_V06_FILE"
        ),
        "inventory_scope": (
            "DECLARATION_CLUSTER" if partial_inventory else "WHOLE_FILE"
        ),
        "snapshot_id": args.snapshot_id,
        "evidence_scope": (
            "CURRENT_SNAPSHOT" if args.snapshot_id is not None
            else "LEGACY_UNTIMED"
        ),
        "fresh_build": current_run_fresh if args.snapshot_id is not None else None,
        "prepare_stage_modes": prepare_modes,
        "prepare_manifest_sha256": (
            sha(args.prepare_manifest) if args.prepare_manifest is not None else None
        ),
        "prepare_run_evidence_sha256": (
            sha(args.prepare_evidence) if args.prepare_evidence is not None else None
        ),
        "source_commit": git(args.source_root, "rev-parse", "HEAD"),
        "source_tree": git(args.source_root, "rev-parse", "HEAD^{tree}"),
        "source_sha256": sha(args.source_root / source_file),
        "source_acquisition_mode": (
            "AUTO_EXTRACT" if source_metadata is not None else "DIRECT_IMPORT"
        ),
        "validation_source_file": validation_source_file,
        "validation_source_sha256": sha(validation_source),
        "source_acquisition_metadata_sha256": source_metadata_sha256,
        "lean_source_sha256": sha(lean_source),
        "fresh_olean_sha256": sha(olean),
        "export_sha256": sha(export),
        "imported_vo_sha256": sha(imported_vo),
        "source_validation_vo_sha256": sha(source_vo),
        "official_source_vo_sha256": (
            sha(source_vo) if validation_source_file == source_file else None
        ),
        "baseline_audit": baseline,
        "additional_evidence": additional_evidence,
        "tooling": {
            "lean4export_base_commit": git(args.exporter_root, "rev-parse", "HEAD"),
            "lean4export_binary_sha256": sha(
                args.exporter_root / ".lake/build/bin/lean4export"
            ),
            "rocq_lean_import_base_commit": git(args.importer_root, "rev-parse", "HEAD"),
            "rocq_lean_import_plugin_sha256": sha(
                args.importer_root / "src/lean_import.cmxs"
            ),
            "rocq_lean_import_foundation_sha256": sha(
                args.importer_root / "src/Lean.vo"
            ),
        },
        "declarations": rows,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2, sort_keys=False) + "\n")
    print(args.output)


if __name__ == "__main__":
    main()
