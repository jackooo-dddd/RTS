#!/usr/bin/env python3
"""Audit a pre-freeze semantic-operation inventory.

The input is intentionally declarative.  It does not infer that a similarly
named lemma is a bridge: every operation must name certified evidence, and
every evidence byte is checked against a recorded SHA-256.  Missing operations
are emitted as explicit obligations and make the command fail closed.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any


ALLOWED_STATUSES = {
    "CERTIFIED",
    "CERTIFIED_WITH_PROP_SPROP_FOUNDATION",
}
ALLOWED_BINDINGS = {"PARAMETRIC_CERTIFIED", "ACTUAL_ARTIFACT"}


def sha(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def canonical_digest(value: object) -> str:
    raw = json.dumps(
        value, sort_keys=True, separators=(",", ":"), ensure_ascii=False
    ).encode()
    return hashlib.sha256(raw).hexdigest()


def resolve(root: Path, value: str) -> Path:
    if not value or Path(value).is_absolute():
        raise SystemExit(f"inventory path must be nonempty and relative: {value}")
    root = root.resolve()
    path = (root / value).resolve()
    try:
        path.relative_to(root)
    except ValueError as exc:
        raise SystemExit(f"inventory path escapes workspace: {value}") from exc
    return path


def check_evidence(root: Path, spec: dict[str, Any], label: str) -> dict[str, str]:
    path = resolve(root, spec.get("path", ""))
    expected = spec.get("sha256", "")
    if len(expected) != 64:
        raise SystemExit(f"{label}: expected SHA-256 is missing or malformed")
    if not path.is_file() or path.stat().st_size == 0:
        raise SystemExit(f"{label}: evidence missing or empty: {path}")
    actual = sha(path)
    if actual != expected:
        raise SystemExit(
            f"{label}: evidence hash mismatch: expected {expected}, got {actual}"
        )
    return {"path": spec["path"], "sha256": actual}


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", required=True, type=Path)
    parser.add_argument("--config", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument(
        "--allow-missing",
        action="store_true",
        help="write obligations without returning a failing exit status",
    )
    args = parser.parse_args()

    root = args.root.resolve()
    config_path = args.config.resolve()
    if not config_path.is_file():
        raise SystemExit(f"operation inventory config missing: {config_path}")
    config = json.loads(config_path.read_text())
    if config.get("schema_version") != 1:
        raise SystemExit("unsupported operation inventory schema")
    declarations = config.get("declarations", [])
    bridges = config.get("certified_bridges", {})
    if not declarations:
        raise SystemExit("operation inventory contains no declarations")

    checked_inputs = [
        check_evidence(root, item, f"snapshot input {item.get('name', '?')}")
        | {"name": item.get("name", "")}
        for item in config.get("snapshot_inputs", [])
    ]
    checked_bridges: dict[str, Any] = {}
    invalid_bridges: dict[str, str] = {}
    for operation, bridge in sorted(bridges.items()):
        status = bridge.get("status")
        binding = bridge.get("binding")
        if status not in ALLOWED_STATUSES:
            invalid_bridges[operation] = f"uncertified status: {status}"
            continue
        if binding not in ALLOWED_BINDINGS:
            invalid_bridges[operation] = f"invalid binding: {binding}"
            continue
        evidence_specs = bridge.get("evidence", [])
        if not evidence_specs:
            invalid_bridges[operation] = "no certificate evidence"
            continue
        checked = [
            check_evidence(root, item, f"bridge {operation}")
            for item in evidence_specs
        ]
        artifact_specs = bridge.get("actual_artifact_evidence", [])
        if binding == "ACTUAL_ARTIFACT" and not artifact_specs:
            invalid_bridges[operation] = "actual-artifact binding has no artifact evidence"
            continue
        artifacts = [
            check_evidence(root, item, f"bridge artifact {operation}")
            for item in artifact_specs
        ]
        checked_bridges[operation] = {
            "status": status,
            "binding": binding,
            "evidence": checked,
            "actual_artifact_evidence": artifacts,
            "certificate_names": bridge.get("certificate_names", []),
        }

    seen: set[str] = set()
    rows: list[dict[str, Any]] = []
    missing_by_declaration: dict[str, list[str]] = {}
    for declaration in declarations:
        name = declaration.get("name", "")
        if not name or name in seen:
            raise SystemExit(f"missing or duplicate declaration name: {name}")
        seen.add(name)
        operations = declaration.get("operations", [])
        if len(operations) != len(set(operations)):
            raise SystemExit(f"duplicate operation in declaration: {name}")
        missing = sorted(
            operation
            for operation in operations
            if operation not in checked_bridges
        )
        if missing:
            missing_by_declaration[name] = missing
        rows.append(
            {
                "name": name,
                "cluster": declaration.get("cluster"),
                "operations": operations,
                "covered_operations": sorted(set(operations) - set(missing)),
                "missing_operations": missing,
            }
        )

    all_operations = sorted(
        {operation for row in declarations for operation in row.get("operations", [])}
    )
    missing_operations = sorted(
        {item for values in missing_by_declaration.values() for item in values}
    )
    result = {
        "schema_version": 1,
        "scope": config.get("scope"),
        "config_sha256": sha(config_path),
        "inventory_fingerprint": canonical_digest(config),
        "snapshot_inputs": checked_inputs,
        "declaration_count": len(rows),
        "operation_count": len(all_operations),
        "covered_operation_count": len(all_operations) - len(missing_operations),
        "missing_operation_count": len(missing_operations),
        "missing_operations": missing_operations,
        "missing_by_declaration": missing_by_declaration,
        "invalid_bridges": invalid_bridges,
        "certified_bridges": checked_bridges,
        "declarations": rows,
        "status": "PASS"
        if not missing_operations and not invalid_bridges
        else "BLOCKED_MISSING_OPERATION_BRIDGE",
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    if result["status"] != "PASS" and not args.allow_missing:
        for operation in missing_operations:
            print(f"missing operation bridge: {operation}")
        for operation, reason in sorted(invalid_bridges.items()):
            print(f"missing operation bridge: {operation} ({reason})")
        raise SystemExit(2)
    print(args.output)


if __name__ == "__main__":
    main()
