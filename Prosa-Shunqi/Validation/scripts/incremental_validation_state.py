#!/usr/bin/env python3
"""Fail-closed, content-addressed state shared by Prosa validators.

The tool deliberately does not decide semantic correctness.  It binds a
prepare/check/finalize run to declared inputs, records stage timings, seals
prepared outputs, and verifies every cached byte before reuse.  Per-file
validators still own source extraction, export interfaces, certificates, and
the acceptance audit.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
import time
from pathlib import Path
from typing import Any


SCHEMA_VERSION = 1
STAGES = (
    "lean_build",
    "source_acquisition",
    "export",
    "rocq_import",
    "certificate_compile",
    "assumption_audit",
    "publication",
)
MODES = ("FRESH", "VERIFIED_CACHE", "FAILED", "SKIPPED")


def sha(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def digest(value: object) -> str:
    encoded = json.dumps(
        value, sort_keys=True, separators=(",", ":"), ensure_ascii=False
    ).encode()
    return hashlib.sha256(encoded).hexdigest()


def require_file(path: Path) -> None:
    if not path.is_file() or path.stat().st_size == 0:
        raise SystemExit(f"required file absent or empty: {path}")


def parse_assignments(values: list[str]) -> dict[str, str]:
    result: dict[str, str] = {}
    for item in values:
        if "=" not in item:
            raise SystemExit(f"expected NAME=VALUE: {item}")
        name, value = item.split("=", 1)
        if not name or name in result:
            raise SystemExit(f"invalid or duplicate name: {name}")
        result[name] = value
    return result


def resolve(roots: dict[str, str], spec: dict[str, Any]) -> Path:
    root = spec.get("root")
    if root not in roots:
        raise SystemExit(f"unknown descriptor root: {root}")
    path = (Path(roots[root]) / spec.get("path", "")).resolve()
    root_path = Path(roots[root]).resolve()
    try:
        path.relative_to(root_path)
    except ValueError as exc:
        raise SystemExit(f"descriptor path escapes root {root}: {path}") from exc
    return path


def tree_hashes(path: Path, suffixes: list[str]) -> dict[str, str]:
    if not path.is_dir():
        raise SystemExit(f"required input tree absent: {path}")
    result: dict[str, str] = {}
    for child in sorted(path.rglob("*")):
        if not child.is_file():
            continue
        if suffixes and not any(child.name.endswith(s) for s in suffixes):
            continue
        result[child.relative_to(path).as_posix()] = sha(child)
    if not result:
        raise SystemExit(f"declared input tree is empty: {path}")
    return result


def run_command(argv: list[str], cwd: Path | None = None) -> str:
    if not argv:
        raise SystemExit("empty command input")
    return subprocess.check_output(argv, cwd=cwd, text=True).strip()


def descriptor(args: argparse.Namespace) -> None:
    roots = parse_assignments(args.root)
    bindings = parse_assignments(args.binding)
    config_path = args.config.resolve()
    require_file(config_path)
    config = json.loads(config_path.read_text())
    files: dict[str, str] = {"descriptor_config": sha(config_path)}
    trees: dict[str, dict[str, str]] = {}
    git_states: dict[str, dict[str, str]] = {}
    commands: dict[str, str] = {}

    for spec in config.get("inputs", []):
        name = spec["name"]
        if name in files:
            raise SystemExit(f"duplicate descriptor input: {name}")
        path = resolve(roots, spec)
        require_file(path)
        files[name] = sha(path)

    for spec in config.get("input_trees", []):
        name = spec["name"]
        if name in trees:
            raise SystemExit(f"duplicate descriptor tree: {name}")
        trees[name] = tree_hashes(resolve(roots, spec), spec.get("suffixes", []))

    for spec in config.get("git_repositories", []):
        name = spec["name"]
        path = resolve(roots, spec)
        state = {
            "head": run_command(["git", "-C", str(path), "rev-parse", "HEAD"]),
            "tree": run_command(
                ["git", "-C", str(path), "rev-parse", "HEAD^{tree}"]
            ),
        }
        if spec.get("require_clean", False):
            status = run_command(
                ["git", "-C", str(path), "status", "--porcelain", "--untracked-files=all"]
            )
            if status:
                raise SystemExit(f"descriptor git repository is dirty: {name}")
            state["clean"] = "true"
        git_states[name] = state

    for spec in config.get("command_inputs", []):
        name = spec["name"]
        cwd = resolve(roots, spec["cwd"]) if spec.get("cwd") else None
        commands[name] = run_command([str(x) for x in spec["argv"]], cwd)

    inputs = {
        "schema_version": SCHEMA_VERSION,
        "scope": config["scope"],
        "files": files,
        "trees": trees,
        "git_repositories": git_states,
        "command_inputs": commands,
        "bindings": bindings,
        "module_loading": config.get("module_loading", {}),
        "prepared_outputs": config.get("prepared_outputs", {}),
    }
    result = {"snapshot_id": digest(inputs), "inputs": inputs}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(result["snapshot_id"])


def output_hashes(values: list[str]) -> dict[str, str]:
    result: dict[str, str] = {}
    for name, value in parse_assignments(values).items():
        path = Path(value).resolve()
        require_file(path)
        result[name] = sha(path)
    return result


def record(args: argparse.Namespace) -> None:
    if args.end_ns < args.start_ns:
        raise SystemExit("stage end precedes stage start")
    entry: dict[str, Any] = {
        "stage": args.stage,
        "mode": args.mode,
        "executed": args.executed == "true",
        "status": args.status,
        "duration_seconds": round((args.end_ns - args.start_ns) / 1_000_000_000, 6),
        "start_ns": args.start_ns,
        "end_ns": args.end_ns,
        "input_fingerprint": args.input_fingerprint,
        "output_hashes": output_hashes(args.output_file),
    }
    if args.failure_reason:
        entry["failure_reason"] = args.failure_reason
    if args.status == "PASS" and args.mode == "FAILED":
        raise SystemExit("FAILED stage cannot have PASS status")
    args.output.parent.mkdir(parents=True, exist_ok=True)
    with args.output.open("a") as stream:
        stream.write(json.dumps(entry, sort_keys=True) + "\n")


def load_events(paths: list[Path]) -> list[dict[str, Any]]:
    events: list[dict[str, Any]] = []
    for path in paths:
        if not path.is_file():
            raise SystemExit(f"stage event log missing: {path}")
        events.extend(json.loads(line) for line in path.read_text().splitlines() if line)
    return events


def finish_run(args: argparse.Namespace) -> None:
    events = load_events(args.events)
    by_stage: dict[str, dict[str, Any]] = {}
    for event in events:
        bucket = by_stage.setdefault(
            event["stage"],
            {"execution_count": 0, "cache_hit_count": 0, "elapsed_seconds": 0.0},
        )
        bucket["execution_count"] += int(bool(event["executed"]))
        bucket["cache_hit_count"] += int(event["mode"] == "VERIFIED_CACHE")
        bucket["elapsed_seconds"] += float(event["duration_seconds"])
    for bucket in by_stage.values():
        bucket["elapsed_seconds"] = round(bucket["elapsed_seconds"], 6)
    result = {
        "schema_version": SCHEMA_VERSION,
        "snapshot_id": args.snapshot_id,
        "run_mode": args.run_mode,
        "recorded_at_unix_ns": time.time_ns(),
        "stages": events,
        "stage_summary": by_stage,
        "executed_stage_count": sum(bool(e["executed"]) for e in events),
        "verified_cache_hit_count": sum(e["mode"] == "VERIFIED_CACHE" for e in events),
        "failed_stage_count": sum(e.get("status") != "PASS" for e in events),
        "total_measured_seconds": round(
            sum(float(e["duration_seconds"]) for e in events), 6
        ),
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")


def prepared_outputs(descriptor_data: dict[str, Any]) -> dict[str, list[str]]:
    groups = descriptor_data.get("inputs", {}).get("prepared_outputs", {})
    if not groups:
        raise SystemExit("descriptor contains no prepared outputs")
    return groups


def seal(args: argparse.Namespace) -> None:
    desc = json.loads(args.descriptor.read_text())
    outputs: dict[str, dict[str, Any]] = {}
    for stage, paths in prepared_outputs(desc).items():
        entries: dict[str, str] = {}
        for rel in paths:
            path = args.prepared / rel
            require_file(path)
            entries[rel] = sha(path)
        outputs[stage] = {"files": entries, "output_set_sha256": digest(entries)}
    result = {
        "schema_version": SCHEMA_VERSION,
        "snapshot_id": desc["snapshot_id"],
        "descriptor_sha256": sha(args.descriptor),
        "input_descriptor": desc,
        "created_at_unix_ns": time.time_ns(),
        "outputs": outputs,
        "fresh_stage_evidence": load_events([args.events]),
    }
    path = args.prepared / "prepare_manifest.json"
    path.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(path)


def verify(args: argparse.Namespace) -> None:
    desc = json.loads(args.descriptor.read_text())
    manifest_path = args.prepared / "prepare_manifest.json"
    require_file(manifest_path)
    manifest = json.loads(manifest_path.read_text())
    if manifest.get("snapshot_id") != desc.get("snapshot_id"):
        raise SystemExit("PREPARED_SNAPSHOT_INPUT_MISMATCH")
    if manifest.get("input_descriptor") != desc:
        raise SystemExit("PREPARED_SNAPSHOT_DESCRIPTOR_MISMATCH")
    events: list[dict[str, Any]] = []
    for stage, group in manifest.get("outputs", {}).items():
        started = time.time_ns()
        entries = group.get("files", {})
        if not entries or group.get("output_set_sha256") != digest(entries):
            raise SystemExit(f"PREPARED_ARTIFACT_MANIFEST_CORRUPT:{stage}")
        for rel, expected in entries.items():
            path = args.prepared / rel
            require_file(path)
            if sha(path) != expected:
                raise SystemExit(f"PREPARED_ARTIFACT_HASH_MISMATCH:{stage}:{rel}")
        ended = time.time_ns()
        events.append(
            {
                "stage": stage,
                "mode": "VERIFIED_CACHE",
                "executed": False,
                "status": "PASS",
                "duration_seconds": round((ended - started) / 1_000_000_000, 6),
                "start_ns": started,
                "end_ns": ended,
                "input_fingerprint": desc["snapshot_id"],
                "output_hashes": entries,
            }
        )
    result = {
        "schema_version": SCHEMA_VERSION,
        "snapshot_id": desc["snapshot_id"],
        "run_mode": "INCREMENTAL",
        "recorded_at_unix_ns": time.time_ns(),
        "stages": events,
        "stage_summary": {
            event["stage"]: {
                "execution_count": 0,
                "cache_hit_count": 1,
                "elapsed_seconds": event["duration_seconds"],
            }
            for event in events
        },
        "executed_stage_count": 0,
        "verified_cache_hit_count": len(events),
        "failed_stage_count": 0,
        "total_measured_seconds": round(
            sum(float(e["duration_seconds"]) for e in events), 6
        ),
    }
    args.run_evidence.parent.mkdir(parents=True, exist_ok=True)
    args.run_evidence.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(args.prepared)


def attach_publication(args: argparse.Namespace) -> None:
    result = json.loads(args.result.read_text())
    evidence = json.loads(args.evidence.read_text())
    if result.get("snapshot_id") != args.snapshot_id:
        raise SystemExit("PUBLICATION_RESULT_SNAPSHOT_MISMATCH")
    if evidence.get("snapshot_id") != args.snapshot_id:
        raise SystemExit("PUBLICATION_EVIDENCE_SNAPSHOT_MISMATCH")
    if evidence.get("failed_stage_count"):
        raise SystemExit("PUBLICATION_EVIDENCE_CONTAINS_FAILURE")
    result["finalize_run_evidence"] = {
        "path": str(args.evidence.resolve()),
        "sha256": sha(args.evidence),
        "run_mode": evidence.get("run_mode"),
        "stage_modes": {
            stage["stage"]: stage["mode"] for stage in evidence.get("stages", [])
        },
    }
    args.result.write_text(json.dumps(result, indent=2) + "\n")


def parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser()
    sub = parser.add_subparsers(dest="command", required=True)
    d = sub.add_parser("descriptor")
    d.add_argument("--config", required=True, type=Path)
    d.add_argument("--root", action="append", default=[], required=True)
    d.add_argument("--binding", action="append", default=[])
    d.add_argument("--output", required=True, type=Path)
    d.set_defaults(func=descriptor)

    r = sub.add_parser("record")
    r.add_argument("--output", required=True, type=Path)
    r.add_argument("--stage", required=True, choices=STAGES)
    r.add_argument("--mode", required=True, choices=MODES)
    r.add_argument("--executed", required=True, choices=("true", "false"))
    r.add_argument("--status", default="PASS", choices=("PASS", "FAIL"))
    r.add_argument("--start-ns", type=int, required=True)
    r.add_argument("--end-ns", type=int, required=True)
    r.add_argument("--input-fingerprint", required=True)
    r.add_argument("--output-file", action="append", default=[])
    r.add_argument("--failure-reason")
    r.set_defaults(func=record)

    f = sub.add_parser("finish-run")
    f.add_argument("--events", type=Path, action="append", required=True)
    f.add_argument("--snapshot-id", required=True)
    f.add_argument("--run-mode", required=True)
    f.add_argument("--output", required=True, type=Path)
    f.set_defaults(func=finish_run)

    s = sub.add_parser("seal")
    s.add_argument("--descriptor", required=True, type=Path)
    s.add_argument("--prepared", required=True, type=Path)
    s.add_argument("--events", required=True, type=Path)
    s.set_defaults(func=seal)

    v = sub.add_parser("verify")
    v.add_argument("--descriptor", required=True, type=Path)
    v.add_argument("--prepared", required=True, type=Path)
    v.add_argument("--run-evidence", required=True, type=Path)
    v.set_defaults(func=verify)

    a = sub.add_parser("attach-publication")
    a.add_argument("--result", required=True, type=Path)
    a.add_argument("--evidence", required=True, type=Path)
    a.add_argument("--snapshot-id", required=True)
    a.set_defaults(func=attach_publication)
    return parser


if __name__ == "__main__":
    parsed = parser().parse_args()
    parsed.func(parsed)
