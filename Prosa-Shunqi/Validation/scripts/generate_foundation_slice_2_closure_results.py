#!/usr/bin/env python3
"""Publish content-addressed Slice-2 closure manifest and status."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path


TARGETS = {
    "prosa.util.tactics.neqP": (
        "neqP", "neqP_statement_correspondence_certificate",
        "TacticsClosureCertificate.v",
        "eqType Boolean disequality/reflection <-> carrier Type + imported DecidableEq",
        ["LogicalRelation.v", "EqTypeCorrespondence.v"],
    ),
    "prosa.util.rel.total_over_list": (
        "total_over_list", "total_over_list_correspondence_certificate",
        "RelClosureCertificate.v",
        "ordered seq/List membership plus pointwise Bool-relation correspondence",
        ["LogicalRelation.v", "RelListCorrespondence.v"],
    ),
    "prosa.util.rel.antisymmetric_over_list": (
        "antisymmetric_over_list", "antisymmetric_over_list_correspondence_certificate",
        "RelClosureCertificate.v",
        "ordered seq/List membership, Bool truth, and equality observation correspondence",
        ["LogicalRelation.v", "RelListCorrespondence.v"],
    ),
    "prosa.util.seqset.set": (
        "seqset_set", "seqset_set_correspondence_certificate",
        "SeqsetClosureCertificate.v",
        "bidirectional record relation preserving ordered carrier and uniq/Nodup law",
        ["LogicalRelation.v", "SeqsetCorrespondence.v"],
    ),
    "prosa.util.seqset.set_of": (
        "seqset_set_of", "seqset_set_of_correspondence_certificate",
        "SeqsetClosureCertificate.v",
        "phantom-erasing alias over the bidirectional seqset record relation",
        ["LogicalRelation.v", "SeqsetCorrespondence.v"],
    ),
    "prosa.util.seqset.set_uniq": (
        "seqset_set_uniq", "seqset_set_uniq_statement_correspondence_certificate",
        "SeqsetClosureCertificate.v",
        "MathComp uniq <-> imported List.Nodup under the seqset record relation",
        ["LogicalRelation.v", "SeqsetCorrespondence.v"],
    ),
    "prosa.util.subadditivity.subadditive_at": (
        "subadditive_at", "subadditive_at_correspondence_certificate",
        "SubadditivityClosureCertificate.v",
        "related Nat functions and values; imported recursive add, equality, and <=",
        ["LogicalRelation.v", "SubadditivityNatCorrespondence.v"],
    ),
    "prosa.util.subadditivity.subadditive_until": (
        "subadditive_until", "subadditive_until_correspondence_certificate",
        "SubadditivityClosureCertificate.v",
        "related Nat functions/values with < and subadditive_at composition",
        ["LogicalRelation.v", "SubadditivityNatCorrespondence.v"],
    ),
    "prosa.util.subadditivity.subadditive": (
        "subadditive", "subadditive_correspondence_certificate",
        "SubadditivityClosureCertificate.v",
        "universal Nat logical relation composed from subadditive_at",
        ["LogicalRelation.v", "SubadditivityNatCorrespondence.v"],
    ),
    "prosa.util.subadditivity.subadditive_standard": (
        "subadditive_standard", "subadditive_standard_correspondence_certificate",
        "SubadditivityClosureCertificate.v",
        "related Nat functions with actual imported recursive add and <=",
        ["LogicalRelation.v", "SubadditivityNatCorrespondence.v"],
    ),
    "prosa.util.subadditivity.subadditive_standard_equivalence": (
        "subadditive_standard_equivalence",
        "subadditive_standard_equivalence_statement_certificate",
        "SubadditivityClosureCertificate.v",
        "structural Iff relation composed from both certified definition relations",
        ["LogicalRelation.v", "SubadditivityNatCorrespondence.v"],
    ),
    "prosa.util.subadditivity.subadditive_leq_mul": (
        "subadditive_leq_mul", "subadditive_leq_mul_statement_certificate",
        "SubadditivityClosureCertificate.v",
        "related Nat functions with actual imported recursive multiplication, <, and <=",
        ["LogicalRelation.v", "SubadditivityNatCorrespondence.v"],
    ),
    "prosa.util.supremum.supremum_unfold": (
        "supremum_unfold", "supremum_unfold_statement_correspondence_certificate",
        "SupremumClosureCertificate.v",
        "Option equality composed from certified supremum and choose_superior relations",
        ["LogicalRelation.v", "SupremumTheoremCorrespondence.v", "SupremumCertificate.v"],
    ),
    "prosa.util.supremum.supremum_exists": (
        "supremum_exists", "supremum_exists_statement_correspondence_certificate",
        "SupremumClosureCertificate.v",
        "seq/List membership and Option Boolean-disequality/Lean-Ne correspondence",
        ["LogicalRelation.v", "SupremumTheoremCorrespondence.v", "SupremumCertificate.v"],
    ),
    "prosa.util.supremum.supremum_none": (
        "supremum_none", "supremum_none_statement_correspondence_certificate",
        "SupremumClosureCertificate.v",
        "Option equality premise and ordered seq/List equality conclusion",
        ["LogicalRelation.v", "SupremumTheoremCorrespondence.v", "SupremumCertificate.v"],
    ),
    "prosa.util.supremum.supremum_in": (
        "supremum_in", "supremum_in_statement_correspondence_certificate",
        "SupremumClosureCertificate.v",
        "Option equality premise and seq/List membership conclusion",
        ["LogicalRelation.v", "SupremumTheoremCorrespondence.v", "SupremumCertificate.v"],
    ),
    "prosa.util.supremum.supremum_spec": (
        "supremum_spec", "supremum_spec_statement_correspondence_certificate",
        "SupremumClosureCertificate.v",
        "full higher-order proposition relation for reflexive/total/transitive Bool relation",
        ["LogicalRelation.v", "SupremumTheoremCorrespondence.v", "SupremumCertificate.v"],
    ),
}


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def digest_json(value: object) -> str:
    return hashlib.sha256(json.dumps(value, sort_keys=True).encode()).hexdigest()


def main() -> int:
    p = argparse.ArgumentParser()
    p.add_argument("--validation-root", required=True, type=Path)
    p.add_argument("--work", required=True, type=Path)
    p.add_argument("--assumptions", required=True, type=Path)
    p.add_argument("--source-compatibility", required=True, type=Path)
    p.add_argument("--baseline-check", required=True, type=Path)
    args = p.parse_args()

    pipeline = args.validation_root / "planning/v06_pipeline"
    base = json.loads((pipeline / "foundation_slice_2_manifest.json").read_text())
    audit_all = json.loads(args.assumptions.read_text())
    audits = audit_all["certificates"]
    source_compat = json.loads(args.source_compatibility.read_text())
    baseline = json.loads(args.baseline_check.read_text())
    cert_root = args.validation_root / "certificates/foundation_slice_2_closure"
    common_root = args.validation_root / "certificates/common"

    rows = []
    for old in base["declarations"]:
        row = dict(old)
        qname = row["rocq_declaration"]
        if qname in TARGETS:
            key, cert, cert_file, relation, bridge_files = TARGETS[qname]
            audit = audits[key]
            cert_path = cert_root / cert_file
            cert_vo = args.work / "certificates" / cert_file.replace(".v", ".vo")
            bridge_hashes = {}
            for name in bridge_files:
                candidate = common_root / name
                if not candidate.exists():
                    candidate = args.validation_root / "certificates/foundation_slice_2" / name
                bridge_hashes[name] = sha(candidate)
            row.update({
                "certificate": cert,
                "certificate_module": cert_file,
                "certificate_source_sha256": sha(cert_path),
                "certificate_vo_sha256": sha(cert_vo),
                "semantic_relation": relation,
                "semantic_status": audit["status"],
                "assumption_audit": audit,
                "semantic_premises": audit["semantic_premises"],
                "foundation_dependencies": {
                    "prop_sprop": audit["prop_sprop_foundation"],
                    "importer": audit["importer_foundation"],
                    "rocq_sprop_definitional_uip": audit["rocq_sprop_definitional_uip"],
                    "bridge_source_sha256": bridge_hashes,
                },
                "acceptance": (
                    "ACCEPTED_V06_TRANSLATION"
                    if audit["status"] in {
                        "CERTIFIED", "CERTIFIED_WITH_PROP_SPROP_FOUNDATION"
                    } else "TRANSLATED_NOT_CERTIFIED"
                ),
            })
            row["content_invalidation_key_sha256"] = digest_json({
                "source": row["source_command_sha256"],
                "lean_type": row["lean_type_sha256"],
                "lean_body": row["lean_body_sha256"],
                "olean": row["fresh_olean_sha256"],
                "export": row["export_sha256"],
                "import": row["imported_vo_sha256"],
                "certificate_source": row["certificate_source_sha256"],
                "certificate_vo": row["certificate_vo_sha256"],
                "assumptions": audit["raw_section_sha256"],
                "bridges": bridge_hashes,
            })
        rows.append(row)

    target_rows = [r for r in rows if r["rocq_declaration"] in TARGETS]
    accepted_targets = [r for r in target_rows if r["acceptance"] == "ACCEPTED_V06_TRANSLATION"]
    all_targets_pass = len(accepted_targets) == len(TARGETS)
    all_common_pass = all(
        v["status"] in {"CERTIFIED", "CERTIFIED_WITH_PROP_SPROP_FOUNDATION"}
        for k, v in audits.items() if k.startswith("common_")
    )
    integrity_pass = (
        source_compat["status"] == "PASS"
        and baseline.get("status") == "PASS"
        and all_targets_pass and all_common_pass
    )

    common_artifacts = {}
    for path in sorted(common_root.glob("*.v")):
        if path.name == "PropSPropFoundation.v" or path.name in {
            "LogicalRelation.v", "EqTypeCorrespondence.v",
            "RelListCorrespondence.v", "SeqsetCorrespondence.v",
            "SubadditivityNatCorrespondence.v",
            "SupremumTheoremCorrespondence.v",
        }:
            vo = args.work / "certificates" / path.with_suffix(".vo").name
            common_artifacts[path.name] = {
                "source_sha256": sha(path),
                "compiled_vo_sha256": sha(vo),
            }

    manifest = {
        "slice": "FOUNDATION_SLICE_2_CLOSURE",
        "freeze_policy": base["freeze_policy"],
        "source_commit": base["source_commit"],
        "source_tree": base["source_tree"],
        "toolchain": base["toolchain"],
        "tooling": base["tooling"],
        "fresh_work_directory": str(args.work),
        "fresh_build": True,
        "baseline_freeze_check": baseline,
        "source_compatibility_audit": source_compat,
        "files": base["files"],
        "common_bridge_artifacts": common_artifacts,
        "assumption_audit_sha256": sha(args.assumptions),
        "declarations": rows,
    }
    (pipeline / "foundation_slice_2_closure_manifest.json").write_text(
        json.dumps(manifest, indent=2, sort_keys=False) + "\n"
    )

    target_status_counts: dict[str, int] = {}
    for row in target_rows:
        target_status_counts[row["semantic_status"]] = (
            target_status_counts.get(row["semantic_status"], 0) + 1
        )
    accepted_all_slice2 = sum(
        r.get("acceptance") == "ACCEPTED_V06_TRANSLATION" for r in rows
    )
    per_file = {}
    for source_file in sorted({r["source_file"] for r in rows}):
        group = [r for r in rows if r["source_file"] == source_file]
        accepted = sum(r.get("acceptance") == "ACCEPTED_V06_TRANSLATION" for r in group)
        per_file[source_file] = {
            "public_declarations": len(group),
            "translated": len(group),
            "proof_clean": len(group),
            "certified": accepted,
            "status": "ACCEPTED_V06_FILE" if accepted == len(group) else "PARTIAL_V06_FILE",
        }

    status = {
        "slice": "FOUNDATION_SLICE_2_CLOSURE",
        "FOUNDATION_SLICE_2_CLOSURE_STATUS": "PASS" if integrity_pass else "PARTIAL",
        "closure_targets": len(TARGETS),
        "closure_targets_accepted": len(accepted_targets),
        "closure_status_counts": target_status_counts,
        "semantic_premises": sorted({
            p for r in target_rows for p in r["assumption_audit"]["semantic_premises"]
        }),
        "unexpected_assumptions": sorted({
            p for r in target_rows for p in r["assumption_audit"]["unexpected"]
        }),
        "target_theorem_self_dependency": any(
            r["assumption_audit"]["target_theorem_dependency"] for r in target_rows
        ),
        "source_theorem_self_dependency": any(
            r["assumption_audit"].get("source_theorem_dependency", False)
            for r in target_rows
        ),
        "common_bridges_audit_pass": all_common_pass,
        "source_compatibility_audit": source_compat["status"],
        "baseline_freeze_check": baseline["status"],
        "per_file": per_file,
        "coverage": {
            "accepted_files": 1 + sum(v["status"] == "ACCEPTED_V06_FILE" for v in per_file.values()),
            "authoritative_files": 357,
            "accepted_declarations": 2 + accepted_all_slice2,
            "authoritative_declarations": 2439,
            "translated_but_not_certified": len(rows) - accepted_all_slice2,
            "proof_clean": 2 + len(rows),
            "deferred_external_boundary": 239,
        },
        "READY_FOR_LAYER1_UTILS": "YES" if integrity_pass else "NO",
        "READY_FOR_JOB_FOUNDATION": "NO",
        "job_foundation_reason": (
            "The authoritative file DAG gives behavior/job.v direct dependencies "
            "behavior/time.v and util/all.v; util/all.v and its transitive prerequisites "
            "are not yet accepted."
        ),
    }
    (pipeline / "foundation_slice_2_closure_status.json").write_text(
        json.dumps(status, indent=2, sort_keys=False) + "\n"
    )
    print(json.dumps(status, indent=2))
    return 0 if integrity_pass else 1


if __name__ == "__main__":
    raise SystemExit(main())
