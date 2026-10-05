#!/usr/bin/env python3
"""Import one immutable failed Theorem6 trace into an AutoAgent round.

This runner deliberately does not invoke Prosabuddy, OpenCode, Coq, or any
model. AutoAgent regenerates deterministic trace analysis from the copied raw
JSONL and treats the root summary below as the sole machine-result authority.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import shutil
import tempfile
from pathlib import Path


RESERVATION_FILE = ".autoagent-reservation.json"
TARGET_WORKSPACE = "2005-ECRTS-Theorem6"
SOURCE_TRACE = Path(
    "/home/junyi/results_analysis_baseline/supplementary/Results_for_Table4_agentstudy/"
    "prosabuddy-casestudy/2005-ECRTS-Theorem6_case3/opencode_events.jsonl"
)
SOURCE_SHA256 = "420c30ba3d157627a59ef7e5f5b545be02d9a29be4b8bee8ad3b398d208f97f1"
SOURCE_SIZE = 3_613_275
SOURCE_LINE_COUNT = 808


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def validate_source(source: Path, expected_sha256: str) -> Path:
    if source.is_symlink() or not source.is_file():
        raise RuntimeError(f"Historical trace must be a regular file: {source}")
    resolved = source.resolve(strict=True)
    if sha256_file(resolved) != expected_sha256:
        raise RuntimeError("Historical trace SHA-256 differs from the fixed importer contract")
    if resolved == SOURCE_TRACE and resolved.stat().st_size != SOURCE_SIZE:
        raise RuntimeError("Historical trace size differs from the fixed importer contract")
    return resolved


def consume_reservation(output_dir: Path) -> tuple[Path, str]:
    lexical = output_dir.expanduser().absolute()
    if lexical.is_symlink():
        raise RuntimeError(f"--output-dir itself cannot be a symlink: {lexical}")
    result = lexical.resolve(strict=True)
    if not result.is_dir():
        raise RuntimeError(f"--output-dir must be an existing directory: {result}")
    marker = result / RESERVATION_FILE
    entries = list(result.iterdir())
    if set(entries) != {marker} or marker.is_symlink() or not marker.is_file():
        raise RuntimeError(f"--output-dir must contain only {RESERVATION_FILE}: {result}")
    try:
        payload = json.loads(marker.read_text(encoding="utf-8"))
    except (OSError, UnicodeError, json.JSONDecodeError) as exc:
        raise RuntimeError(f"Invalid AutoAgent reservation marker: {marker}") from exc
    operation_id = payload.get("operation_id") if isinstance(payload, dict) else None
    if (
        not isinstance(payload, dict)
        or payload.get("schema_version") != 1
        or not isinstance(operation_id, str)
        or not operation_id
    ):
        raise RuntimeError(f"Invalid AutoAgent reservation payload: {marker}")
    marker.unlink()
    return result, operation_id


def atomic_copy(source: Path, destination: Path) -> None:
    destination.parent.mkdir(parents=True, exist_ok=False)
    descriptor, temporary = tempfile.mkstemp(
        prefix=f".{destination.name}.", suffix=".tmp", dir=destination.parent
    )
    temporary_path = Path(temporary)
    try:
        with os.fdopen(descriptor, "wb") as output, source.open("rb") as input_stream:
            shutil.copyfileobj(input_stream, output)
            output.flush()
            os.fsync(output.fileno())
        os.replace(temporary_path, destination)
    finally:
        temporary_path.unlink(missing_ok=True)


def atomic_json(path: Path, payload: object) -> None:
    descriptor, temporary = tempfile.mkstemp(
        prefix=f".{path.name}.", suffix=".tmp", dir=path.parent
    )
    temporary_path = Path(temporary)
    try:
        with os.fdopen(descriptor, "w", encoding="utf-8") as stream:
            json.dump(payload, stream, ensure_ascii=False, indent=2)
            stream.write("\n")
            stream.flush()
            os.fsync(stream.fileno())
        os.replace(temporary_path, path)
    finally:
        temporary_path.unlink(missing_ok=True)


def import_trace(
    output_dir: Path,
    workspace: str,
    *,
    source: Path = SOURCE_TRACE,
    expected_sha256: str = SOURCE_SHA256,
) -> dict[str, object]:
    if workspace != TARGET_WORKSPACE:
        raise RuntimeError(
            f"Historical importer accepts only {TARGET_WORKSPACE!r}, not {workspace!r}"
        )
    frozen_source = validate_source(source, expected_sha256)
    result_dir, reservation_operation = consume_reservation(output_dir)
    trace_path = result_dir / workspace / "opencode_events.jsonl"
    atomic_copy(frozen_source, trace_path)
    if trace_path.is_symlink() or sha256_file(trace_path) != expected_sha256:
        raise RuntimeError("Copied historical trace failed post-publication verification")
    line_count = sum(1 for _ in trace_path.open("rb"))
    if frozen_source == SOURCE_TRACE and line_count != SOURCE_LINE_COUNT:
        raise RuntimeError("Historical trace line count differs from the fixed importer contract")
    record: dict[str, object] = {
        "workspace": workspace,
        "status": "historical_failure",
        "has_qed": False,
        "proof_verified": False,
        "historical_trace_imported": True,
        "historical_trace_sha256": expected_sha256,
        "historical_trace_line_count": line_count,
        "failure_basis": "The preserved trace ends with an admitted, unclosed theorem rather than Qed.",
        "runner_invoked_prosabuddy": False,
        "reservation_operation_id": reservation_operation,
    }
    atomic_json(result_dir / "summary.json", [record])
    if any(path.is_symlink() for path in result_dir.rglob("*")):
        raise RuntimeError("Historical import result contains a symlink")
    return record


def parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output-dir", type=Path, required=True)
    parser.add_argument("workspace")
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = parse_args(argv)
    import_trace(args.output_dir, args.workspace)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())