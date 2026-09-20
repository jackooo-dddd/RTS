#!/usr/bin/env python3
"""Generate the conservative Prosa v0.6-centered migration inventory.

This is a planning aid, not a semantic validator.  Prosa v0.6 is always the
target specification.  Historical Rocq and current Lean declarations are
reported only as candidates, and reuse is allowed only with explicit
provenance and source-evolution evidence.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import importlib.util
import json
import re
import subprocess
from collections import Counter, defaultdict
from difflib import SequenceMatcher
from pathlib import Path
from typing import Any

V06 = "414e66760333eaa4ef78c685bcf53291c527a548"
V04 = "ee05f255e29676ad79e07b5d6cc59dc66cd7fcb7"
THEOREMS = {"Lemma", "Theorem", "Corollary", "Fact", "Remark", "Proposition", "Example"}
STRUCTURES = {"Class", "Record", "Structure", "Inductive", "Variant", "CoInductive"}

LEAN_DECL_RE = re.compile(
    r"(?m)^[ \t]*(?:@\[[^\n]*\]\s*)*(?P<mods>(?:(?:private|protected|noncomputable|partial|unsafe|opaque)\s+)*)"
    r"(?P<kind>def|abbrev|theorem|lemma|class|structure|inductive|instance)"
    r"(?:\s+(?:@[A-Za-z_][A-Za-z0-9_'.]*\s*)?)(?P<name>[A-Za-z_][A-Za-z0-9_']*)"
)
SOURCE_RE = re.compile(r"Translated from:\s*(?:\.\./rt-proofs/)?([^\s]+\.v)")


def sha(text: str) -> str:
    return hashlib.sha256(text.encode()).hexdigest()


def norm(text: str, strip_comments) -> str:
    return " ".join(strip_comments(text).split())


def read_csv(path: Path) -> list[dict[str, str]]:
    with path.open(newline="") as f:
        return list(csv.DictReader(f))


def write_csv(path: Path, fields: list[str], rows: list[dict[str, Any]]) -> None:
    with path.open("w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=fields, extrasaction="ignore", lineterminator="\n")
        w.writeheader(); w.writerows(rows)


def load_extractor(path: Path):
    spec = importlib.util.spec_from_file_location("v06_inventory", path)
    assert spec and spec.loader
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def source_declarations(root: Path, extractor) -> tuple[list[dict[str, Any]], list[dict[str, Any]]]:
    files: list[dict[str, Any]] = []
    decls: list[dict[str, Any]] = []
    for path in sorted(root.rglob("*.v")):
        rel = path.relative_to(root).as_posix()
        raw = path.read_text(errors="replace")
        category, group, reason = extractor.classify_file(rel)
        files.append({
            "v04_file": rel, "module": extractor.module_of(rel), "category": category,
            "build_group": group, "classification_reason": reason,
            "sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
            "lines": len(raw.splitlines()),
        })
        parsed = extractor.parse_declarations(path, extractor.module_of(rel))
        for d in parsed:
            d["source_file"] = rel
            command = raw[d["start_char"]:d["end_char"]]
            header = raw[d["start_char"]:d["header_end_char"]]
            normalized = norm(command, extractor.strip_comments)
            normalized_header = norm(header, extractor.strip_comments)
            if d["assignment"] is not None:
                # assignment is a byte position; source is ASCII in all matched headers.
                local = header.find(":=")
                signature = norm(header[:local], extractor.strip_comments) if local >= 0 else normalized_header
                body = norm(header[local + 2:], extractor.strip_comments) if local >= 0 else ""
            else:
                signature, body = normalized_header, ""
            d.update({
                "normalized_command": normalized,
                "command_fingerprint": "source-command-sha256:" + sha(normalized),
                "signature_fingerprint": "source-signature-sha256:" + sha(signature),
                "body_fingerprint": ("source-body-sha256:" + sha(body)) if body else "",
                "structure_fields_json": json.dumps(d["structure_fields"], separators=(",", ":")),
            })
            decls.append(d)
    return files, decls


def strip_lean_comments(text: str) -> str:
    # Preserve line count and approximate offsets; declaration names are the only
    # facts extracted from Lean here.
    text = re.sub(r"/-(?:.|\n)*?-/", lambda m: "\n" * m.group(0).count("\n"), text)
    return re.sub(r"--[^\n]*", "", text)


def scan_lean(root: Path) -> list[dict[str, str]]:
    rows: list[dict[str, str]] = []
    for path in sorted(root.rglob("*.lean")):
        rel = path.relative_to(root).as_posix()
        raw = path.read_text(errors="replace")
        clean = strip_lean_comments(raw)
        sm = SOURCE_RE.search(raw)
        source = sm.group(1) if sm else ""
        matches = list(LEAN_DECL_RE.finditer(clean))
        for i, m in enumerate(matches):
            if "private" in (m.group("mods") or "").split():
                continue
            end = matches[i + 1].start() if i + 1 < len(matches) else len(clean)
            snippet = clean[m.end():end]
            name, kind = m.group("name"), m.group("kind")
            rows.append({
                "lean_file": rel, "lean_declaration": name, "lean_kind": kind.upper(),
                "lean_owner": "", "translated_from": source,
                "is_classic": str(rel.startswith("Classic/")),
            })
            if kind in {"class", "structure"}:
                for fm in re.finditer(r"(?m)^[ \t]{2,}([A-Za-z_][A-Za-z0-9_']*)\s*(?:\([^\n]*\)\s*)?:", snippet):
                    rows.append({
                        "lean_file": rel, "lean_declaration": fm.group(1), "lean_kind": "FIELD",
                        "lean_owner": name, "translated_from": source,
                        "is_classic": str(rel.startswith("Classic/")),
                    })
            if kind == "inductive":
                for cm in re.finditer(r"(?m)^[ \t]*\|\s*([A-Za-z_][A-Za-z0-9_']*)", snippet):
                    rows.append({
                        "lean_file": rel, "lean_declaration": cm.group(1), "lean_kind": "CONSTRUCTOR",
                        "lean_owner": name, "translated_from": source,
                        "is_classic": str(rel.startswith("Classic/")),
                    })
    return rows


def comparable_kind(a: str, b: str) -> bool:
    groups = [THEOREMS, STRUCTURES, {"Definition", "Fixpoint", "CoFixpoint", "Instance"}]
    return a == b or any(a in g and b in g for g in groups)


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--repo-root", type=Path, required=True)
    ap.add_argument("--v04-root", type=Path, required=True)
    ap.add_argument("--v06-root", type=Path, required=True)
    ap.add_argument("--dependency", type=Path, required=True)
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    args.output.mkdir(parents=True, exist_ok=True)

    extractor = load_extractor(args.dependency / "generate_v06_inventory.py")
    v04_files, v04 = source_declarations(args.v04_root, extractor)
    _, v06_source = source_declarations(args.v06_root, extractor)
    v06_source_by_key = {(d["source_file"], d["declaration_name"]): d for d in v06_source}
    v06_inventory = read_csv(args.dependency / "declaration_inventory.csv")
    v06_layers = {r["qualified_name"]: r for r in read_csv(args.dependency / "declaration_layers.csv")}
    v06_file_rows = {r["file"]: r for r in read_csv(args.dependency / "file_inventory.csv")}

    v04_by_key = {(d["source_file"], d["declaration_name"]): d for d in v04}
    v04_by_name: dict[str, list[dict[str, Any]]] = defaultdict(list)
    v04_fields: dict[tuple[str, str], list[tuple[dict[str, Any], dict[str, str]]]] = defaultdict(list)
    for d in v04:
        v04_by_name[d["declaration_name"]].append(d)
        for field in d["structure_fields"]:
            v04_fields[(d["source_file"], field["name"])].append((d, field))

    lean = scan_lean(args.repo_root / "Prosa")
    lean_by_source_name: dict[tuple[str, str], list[dict[str, str]]] = defaultdict(list)
    lean_by_name: dict[str, list[dict[str, str]]] = defaultdict(list)
    for x in lean:
        if x["translated_from"]:
            lean_by_source_name[(x["translated_from"], x["lean_declaration"])].append(x)
        lean_by_name[x["lean_declaration"]].append(x)

    # Reuse of the previous provenance audit is restricted to its demonstrated
    # fact: non-Classic Translated-from paths are v0.4 fingerprints.
    provenance_json = args.repo_root / "Validation/reports/logs/prosa_source_provenance_2026-09-20/tag_fingerprints.json"
    audited_paths: set[str] = set()
    if provenance_json.exists():
        p = json.loads(provenance_json.read_text())
        audited_paths = {x["source_path"] for x in p["files"] if x["revision"] == "v0.4" and x["path_exists"]}

    foundation_keys = {
        ("behavior/time.v", "instant"), ("behavior/time.v", "duration"),
        ("behavior/job.v", "JobType"), ("behavior/job.v", "work"),
        ("behavior/job.v", "JobArrival"), ("behavior/job.v", "JobCost"),
        ("behavior/schedule.v", "ProcessorState"), ("behavior/schedule.v", "scheduled_in"),
        ("behavior/schedule.v", "supply_in"), ("behavior/schedule.v", "service_in"),
        ("behavior/service.v", "service_at"), ("behavior/service.v", "service_during"),
        ("behavior/service.v", "service"), ("behavior/service.v", "completed_by"),
        ("behavior/service.v", "completes_at"), ("model/task/concept.v", "TaskType"),
        ("model/task/concept.v", "JobTask"),
        ("behavior/arrival_sequence.v", "arrivals_at"),
        ("behavior/arrival_sequence.v", "arrivals_between"),
    }
    policy_for = {
        "instant": "NAT_TIME", "duration": "NAT_TIME", "work": "NAT_WORK",
        "JobType": "EQTYPE_CARRIER_PLUS_DECIDABLE_EQ", "TaskType": "EQTYPE_CARRIER_PLUS_DECIDABLE_EQ",
        "JobArrival": "CLASS_FIELDS_AND_LAWS", "JobCost": "CLASS_FIELDS_AND_LAWS",
        "JobTask": "CLASS_FIELDS_AND_LAWS", "ProcessorState": "PROCESSOR_STATE_NESTED_CARRIERS",
        "scheduled_in": "BOOL_FINITE_EXISTENTIAL", "supply_in": "FINITE_CORE_SUM",
        "service_in": "FINITE_CORE_SUM", "service_at": "SERVICE_CHAIN",
        "service_during": "HALF_OPEN_INTERVAL_SUM", "service": "HALF_OPEN_INTERVAL_SUM",
        "completed_by": "PROP_FROM_NAT_ORDER", "completes_at": "BOOL_ZERO_CASE_AND_COMPLETION",
        "arrivals_at": "SEQ_AS_LIST", "arrivals_between": "SEQ_AS_LIST_BIGCAT",
    }
    external_files = {f for f, r in v06_file_rows.items() if r["build_group"] == "refinements"}

    used_v04: set[str] = set()
    rows: list[dict[str, Any]] = []
    for v in v06_inventory:
        key = (v["source_file"], v["declaration_name"])
        src = v06_source_by_key[key]
        old: dict[str, Any] | None = v04_by_key.get(key)
        counterpart_status = "NONE"
        evidence: list[str] = []
        secondary: list[str] = []
        field_owner = ""

        if old:
            counterpart_status = "VERIFIED_SAME_FILE_SAME_NAME"
            evidence.append("same file and declaration name")
        elif v04_fields.get(key):
            owner, field = v04_fields[key][0]
            old = owner
            field_owner = owner["declaration_name"]
            counterpart_status = "VERIFIED_STRUCTURE_FIELD_ANCESTOR"
            evidence.append(f"v0.4 {field_owner} field {field['name']} became/relates to a v0.6 declaration")
        else:
            same = [d for d in v04_by_name.get(v["declaration_name"], []) if comparable_kind(d["kind"], v["kind"])]
            exact = [d for d in same if d["normalized_command"] == src["normalized_command"]]
            if len(exact) == 1:
                old = exact[0]
                counterpart_status = "VERIFIED_IDENTICAL_COMMAND_AFTER_MOVE"
                evidence.append("unique same-name compatible-kind declaration with identical normalized command")
            elif len(same) == 1:
                candidate = same[0]
                ratio = SequenceMatcher(None, candidate["normalized_command"], src["normalized_command"]).ratio()
                if ratio >= 0.82:
                    old = candidate
                    counterpart_status = "PROBABLE_MOVED_OR_EVOLVED"
                    evidence.append(f"unique same-name compatible-kind candidate; normalized-command similarity={ratio:.3f}")
                else:
                    old = candidate
                    counterpart_status = "UNCLEAR_NAME_ONLY"
                    evidence.append(f"unique global same name is insufficient; similarity={ratio:.3f}")
            else:
                # Search for an actual rename inside the same surviving file.
                pool = [d for d in v04 if d["source_file"] == v["source_file"] and comparable_kind(d["kind"], v["kind"])]
                scored = sorted(((SequenceMatcher(None, d["normalized_command"].replace(d["declaration_name"], "<NAME>", 1),
                                                      src["normalized_command"].replace(v["declaration_name"], "<NAME>", 1)).ratio(), d)
                                 for d in pool), reverse=True, key=lambda x: x[0])
                if scored and scored[0][0] >= 0.92 and (len(scored) == 1 or scored[0][0] - scored[1][0] >= 0.05):
                    old = scored[0][1]
                    counterpart_status = "VERIFIED_RENAME_BY_COMMAND_SHAPE"
                    evidence.append(f"same-file unique normalized command-shape match={scored[0][0]:.3f}")

        if old and counterpart_status != "UNCLEAR_NAME_ONLY":
            used_v04.add(old["qualified_name"])

        if old is None:
            change_class = "NEW_IN_V06"
            evidence.append("no credible v0.4 declaration or structure-field ancestor found")
        elif counterpart_status == "UNCLEAR_NAME_ONLY":
            change_class = "UNCLEAR"
        elif field_owner:
            change_class = "SPLIT_OR_MERGED"
            secondary.append("source class field was externalized/re-derived in v0.6")
        elif old["normalized_command"] == src["normalized_command"]:
            change_class = "UNCHANGED_FROM_V04" if old["source_file"] == v["source_file"] else "MOVED_OR_RENAMED"
        elif old["source_file"] != v["source_file"] and counterpart_status.startswith("VERIFIED"):
            change_class = "MOVED_OR_RENAMED"
            secondary.append("normalized declaration also changed")
        elif v["kind"] in STRUCTURES:
            change_class = "EVOLVED_STRUCTURE"
            secondary.append("structure command/fields differ")
        elif v["kind"] in THEOREMS:
            change_class = "EVOLVED_SIGNATURE"
            secondary.append("theorem statement differs; proof bodies are not compared")
        elif old["signature_fingerprint"] == src["signature_fingerprint"]:
            change_class = "EVOLVED_DEFINITION"
            secondary.append("public signature stable; computational body changed")
        else:
            change_class = "EVOLVED_SIGNATURE"
            secondary.append("binder/type or declaration header changed")

        # Candidate selection first follows the v0.4 source path, then the v0.6
        # path, and only then permits a global name-only hint.
        candidates: list[dict[str, str]] = []
        old_path = old["source_file"] if old else ""
        if old_path:
            candidates = lean_by_source_name.get((old_path, v["declaration_name"]), [])
            if not candidates and old:
                candidates = lean_by_source_name.get((old_path, old["declaration_name"]), [])
        if not candidates:
            candidates = lean_by_source_name.get((v["source_file"], v["declaration_name"]), [])
        if candidates:
            candidate = sorted(candidates, key=lambda x: (x["is_classic"] == "True", x["lean_file"], x["lean_kind"]))[0]
            if candidate["is_classic"] == "True":
                lean_prov = "HISTORICAL_BUT_UNVERIFIED"
            elif candidate["translated_from"] in audited_paths:
                lean_prov = "HIGH_V04_PROVENANCE"
            else:
                lean_prov = "HISTORICAL_BUT_UNVERIFIED"
        else:
            global_candidates = lean_by_name.get(v["declaration_name"], [])
            if len(global_candidates) == 1:
                candidate = global_candidates[0]
                lean_prov = "HISTORICAL_BUT_UNVERIFIED" if candidate["is_classic"] == "True" else "NAME_ONLY"
            else:
                candidate = None
                lean_prov = "NONE"

        foundation = key in foundation_keys
        review = False
        if v["source_file"] in external_files:
            reuse = "DEFER_EXTERNAL_BOUNDARY"
        elif change_class == "UNCLEAR":
            reuse, review = "REVIEW_REQUIRED", True
        elif candidate is None:
            reuse = "NEW_TRANSLATION"
        elif lean_prov in {"NAME_ONLY", "HISTORICAL_BUT_UNVERIFIED"}:
            reuse = "REFERENCE_ONLY"
        elif change_class == "UNCHANGED_FROM_V04":
            reuse = "REUSE_AFTER_REVALIDATION"
        elif change_class in {"EVOLVED_SIGNATURE", "EVOLVED_DEFINITION", "EVOLVED_STRUCTURE", "SPLIT_OR_MERGED", "MOVED_OR_RENAMED"}:
            reuse = "ADAPT_OLD_LEAN"
        else:
            reuse = "REFERENCE_ONLY"

        # Hand-audited foundational corrections.  These prevent mechanically
        # stable names from hiding representation or transitive semantic drift.
        name = v["declaration_name"]
        if name in {"JobType", "TaskType"}:
            reuse = "ADAPT_OLD_LEAN"
            secondary.append("Lean carrier representation must explicitly provide DecidableEq")
        if name == "ProcessorState":
            reuse = "ADAPT_OLD_LEAN" if candidate else "NEW_TRANSLATION"
            secondary.append("v0.6 adds nested State, per-core supply/service, and two laws")
        if name == "service_in" and v["source_file"] == "behavior/schedule.v":
            reuse = "REFERENCE_ONLY" if candidate else "NEW_TRANSLATION"
            secondary.append("old/current field is not the v0.6 derived per-core sum")
        if name in {"scheduled_in", "service_at", "service_during", "service", "completed_by", "completes_at"}:
            if candidate:
                reuse = "ADAPT_OLD_LEAN"
            secondary.append("must be rechecked after the v0.6 ProcessorState/service-chain representation is fixed")
        if name == "supply_in" and v["source_file"] == "behavior/schedule.v":
            reuse = "NEW_TRANSLATION"

        if review and not secondary:
            secondary.append("counterpart ambiguity requires human review")
        confidence = (
            "HIGH" if reuse == "REUSE_AFTER_REVALIDATION" else
            "MEDIUM" if reuse == "ADAPT_OLD_LEAN" and lean_prov == "HIGH_V04_PROVENANCE" else
            "LOW" if reuse in {"REFERENCE_ONLY", "REVIEW_REQUIRED"} else
            "N/A" if reuse == "DEFER_EXTERNAL_BOUNDARY" else "MEDIUM"
        )
        layer = v06_layers[v["qualified_name"]]
        row = {
            "v06_file": v["source_file"], "v06_declaration": v["declaration_name"],
            "v06_qualified_name": v["qualified_name"], "v06_kind": v["kind"],
            "v06_layer": layer["layer"], "v06_type_fingerprint": v["final_type_or_type_fingerprint"],
            "v06_type_evidence_status": v["type_evidence_status"],
            "v06_dependency_confidence": layer["dependency_extraction_confidence"],
            "v04_file": old["source_file"] if old else "",
            "v04_declaration": (f"{field_owner}.{v['declaration_name']}" if field_owner else old["declaration_name"] if old else ""),
            "v04_kind": ("STRUCTURE_FIELD" if field_owner else old["kind"] if old else ""),
            "v04_counterpart_status": counterpart_status,
            "v04_to_v06_class": change_class,
            "secondary_notes": "; ".join(dict.fromkeys(secondary)),
            "change_evidence": "; ".join(evidence),
            "lean_file": candidate["lean_file"] if candidate else "",
            "lean_declaration": ((candidate["lean_owner"] + ".") if candidate and candidate["lean_owner"] else "") + (candidate["lean_declaration"] if candidate else ""),
            "lean_kind": candidate["lean_kind"] if candidate else "",
            "lean_candidate_provenance": lean_prov,
            "reuse_action": reuse, "reuse_confidence": confidence,
            "reason": "; ".join(dict.fromkeys(evidence + secondary)) or "conservative inventory mapping",
            "foundation_sensitive": str(foundation),
            "representation_policy": policy_for.get(name, "DEFAULT_DECLARATION_FIDELITY"),
            "review_required": str(review),
            "external_boundary": str(v["source_file"] in external_files),
        }
        rows.append(row)

    fields = list(rows[0])
    write_csv(args.output / "v06_migration_table.csv", fields, rows)
    (args.output / "v06_migration_table.json").write_text(json.dumps(rows, indent=2, sort_keys=True) + "\n")
    write_csv(args.output / "v04_file_inventory.csv", list(v04_files[0]), v04_files)
    v04_rows = [{
        "v04_file": d["source_file"], "v04_declaration": d["declaration_name"],
        "qualified_name": d["qualified_name"], "kind": d["kind"], "source_order": d["source_order"],
        "source_line": d["source_line"], "source_command_fingerprint": d["command_fingerprint"],
        "signature_fingerprint": d["signature_fingerprint"], "body_fingerprint": d["body_fingerprint"],
        "structure_fields": d["structure_fields_json"],
        "type_evidence_status": "SOURCE_COMMAND_FINGERPRINT_ONLY_NOT_ELABORATED",
    } for d in v04]
    write_csv(args.output / "v04_declaration_inventory.csv", list(v04_rows[0]), v04_rows)
    legacy = [{
        "v04_file": d["source_file"], "v04_declaration": d["declaration_name"],
        "qualified_name": d["qualified_name"], "kind": d["kind"],
        "classification": "V04_LEGACY_ONLY_OR_REPLACED",
        "reason": "not selected as a credible ancestor of any v0.6 public declaration",
    } for d in v04 if d["qualified_name"] not in used_v04]
    write_csv(args.output / "v04_legacy_only.csv", list(legacy[0]) if legacy else
              ["v04_file", "v04_declaration", "qualified_name", "kind", "classification", "reason"], legacy)

    changes = Counter(r["v04_to_v06_class"] for r in rows)
    reuse = Counter(r["reuse_action"] for r in rows)
    prov = Counter(r["lean_candidate_provenance"] for r in rows)
    summary = {
        "authority": {"v06_commit": V06, "v04_reference_commit": V04},
        "counts": {
            "v04_files": len(v04_files), "v04_public_declarations": len(v04),
            "v04_legacy_only": len(legacy), "v06_declarations": len(rows),
            "v06_change_class": dict(sorted(changes.items())),
            "reuse_action": dict(sorted(reuse.items())),
            "lean_candidate_provenance": dict(sorted(prov.items())),
            "external_boundary": sum(r["external_boundary"] == "True" for r in rows),
            "foundation_sensitive": sum(r["foundation_sensitive"] == "True" for r in rows),
        },
        "integrity": {
            "v06_exactly_once": len(rows) == len({r["v06_qualified_name"] for r in rows}) == 2439,
            "reuse_rows_have_candidate_and_strong_provenance": all(
                r["lean_file"] and r["lean_candidate_provenance"] in {"HIGH_V04_PROVENANCE", "DIRECT_CURRENT_SOURCE_EVIDENCE"}
                for r in rows if r["reuse_action"] == "REUSE_AFTER_REVALIDATION"),
            "new_in_v06_has_no_credible_v04": all(
                r["v04_counterpart_status"] in {"NONE"} for r in rows if r["v04_to_v06_class"] == "NEW_IN_V06"),
            "review_required_has_reason": all(r["reason"] for r in rows if r["reuse_action"] == "REVIEW_REQUIRED"),
            "all_239_external_retained": sum(r["external_boundary"] == "True" for r in rows) == 239,
        },
        "warnings": [
            "v0.4 types are source-command fingerprints, not elaborated Rocq Check evidence.",
            "Global name-only candidates are never promoted to reuse candidates.",
            "This table is planning evidence, not semantic correspondence certification.",
        ],
    }
    (args.output / "mapping_summary.json").write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n")
    print(json.dumps(summary, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
