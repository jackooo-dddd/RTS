#!/usr/bin/env python3
"""Run Phase-1-only Prosabuddy experiments with a compile-checked skeleton endpoint.

This runner reuses the existing casestudy staging, process supervision, event
capture, retry, and result-directory machinery.  It changes only the endpoint:
a run succeeds when the target theorem has a contract-bearing decomposition,
all pending tactic admits are confined to leaf proof regions, and the complete
file passes ``coqc`` with those admits retained.
"""

from __future__ import annotations

import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
from collections import Counter
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

SCRIPT_DIR = Path(__file__).resolve().parent
EXPERIMENT_ROOT = SCRIPT_DIR.parent
for search_path in (EXPERIMENT_ROOT, SCRIPT_DIR):
    value = str(search_path)
    if value not in sys.path:
        sys.path.insert(0, value)

import run_casestudy_opencode_minprosa as base

COMPLETION_MODE = "decomposition"
REQUIRED_CONTRACT_FIELDS = (
    "plan_node",
    "depends_on",
    "source",
    "input",
    "output",
    "layer",
    "expected",
    "normal_form",
    "evidence",
)
LEAF_KINDS = {
    "definition_rewrite",
    "library_instantiation",
    "semantic_bridge",
    "pointwise_semantic_bridge",
    "witness_transport",
    "witness_extraction",
    "injectivity_uniq",
    "uniqueness_injection",
    "count_cardinality",
    "shape_transport",
    "case_split_boundary",
    "contradiction_close",
    "final_arithmetic",
}
REGION_BEGIN = re.compile(r"\(\*\s*proof_region\s+begin\s+([\s\S]*?)\s*\*\)")
REGION_END = re.compile(r"\(\*\s*proof_region\s+end([\s\S]*?)\*\)")
ATTRIBUTE = re.compile(r"([A-Za-z_][A-Za-z0-9_-]*)\s*:\s*(?:\"([^\"]*)\"|'([^']*)'|([^\s*]+))")
ADMIT_TACTIC = re.compile(r"\b(?:by\s+)?admit\s*\.")
ADMITTED_COMMAND = re.compile(r"\bAdmitted\s*\.")
PROOF_TERMINATOR = re.compile(r"\b(Qed|Defined|Admitted)\s*\.")
DISALLOWED_DECLARATION = re.compile(
    r"^\s*(?:Local\s+)?(Axiom|Hypothesis|Parameter|Variable)\b",
    re.MULTILINE,
)

ORIGINAL_RUN_WORKSPACE = base.run_workspace
ORIGINAL_INVOKE_OPENCODE = base._invoke_opencode
ORIGINAL_WRITE_JSON = base.write_json


def now_iso() -> str:
    return datetime.now(timezone.utc).isoformat()


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def _mask_coq_comments_and_strings(source: str) -> str:
    """Mask comments and strings while preserving source offsets."""
    masked = list(source)
    comment_depth = 0
    in_string = False
    index = 0
    while index < len(source):
        pair = source[index : index + 2]
        if comment_depth:
            if pair == "(*":
                masked[index] = masked[index + 1] = " "
                comment_depth += 1
                index += 2
                continue
            if pair == "*)":
                masked[index] = masked[index + 1] = " "
                comment_depth -= 1
                index += 2
                continue
            if source[index] != "\n":
                masked[index] = " "
            index += 1
            continue
        if in_string:
            if source[index] == '"':
                if index + 1 < len(source) and source[index + 1] == '"':
                    masked[index] = masked[index + 1] = " "
                    index += 2
                    continue
                masked[index] = " "
                in_string = False
                index += 1
                continue
            if source[index] != "\n":
                masked[index] = " "
            index += 1
            continue
        if pair == "(*":
            masked[index] = masked[index + 1] = " "
            comment_depth = 1
            index += 2
            continue
        if source[index] == '"':
            masked[index] = " "
            in_string = True
        index += 1
    return "".join(masked)


def _parse_attributes(text: str) -> dict[str, str]:
    attributes: dict[str, str] = {}
    for match in ATTRIBUTE.finditer(text):
        attributes[match.group(1)] = match.group(2) or match.group(3) or match.group(4) or ""
    return attributes


def _nearby_contract_attributes(source: str, marker_start: int) -> dict[str, str]:
    window = source[max(0, marker_start - 2000) : marker_start]
    comments = list(re.finditer(r"\(\*([\s\S]*?)\*\)", window))
    for comment in reversed(comments):
        text = comment.group(1)
        if any(re.search(rf"\b{re.escape(field)}\s*:", text) for field in REQUIRED_CONTRACT_FIELDS):
            return _parse_attributes(text)
    return {}


def _target_proof_body(source_theorem_file: Path, theorem_file: Path) -> tuple[str, str, tuple[int, int, int, int]]:
    theorem_kind = base.target_theorem_kind(source_theorem_file)
    theorem_name = base.target_theorem_name(source_theorem_file)
    source_text = source_theorem_file.read_text(encoding="utf-8", errors="ignore")
    current_text = theorem_file.read_text(encoding="utf-8", errors="ignore")
    ranges = base._extract_target_theorem_ranges(current_text, theorem_kind, theorem_name)
    if ranges is None:
        source_ranges = base._extract_target_theorem_ranges(source_text, theorem_kind, theorem_name)
        source_suffix = source_text[source_ranges[3] :] if source_ranges else ""
        if source_suffix:
            ranges = base._extract_target_theorem_ranges(
                current_text,
                theorem_kind,
                theorem_name,
                allow_unterminated=True,
                theorem_suffix=source_suffix,
            )
    if ranges is None:
        raise RuntimeError(f"Could not locate target theorem `{theorem_name}` in {theorem_file.name}")
    return theorem_name, current_text, ranges


def analyze_decomposition_structure(source_theorem_file: Path, theorem_file: Path) -> dict[str, Any]:
    """Validate leaf-region structure independently of Coq compilation."""
    theorem_name, current_text, ranges = _target_proof_body(source_theorem_file, theorem_file)
    _decl_start, _statement_end, body_start, body_end = ranges
    proof_body = current_text[body_start:body_end]
    masked_body = _mask_coq_comments_and_strings(proof_body)
    issues: list[str] = []
    regions: list[dict[str, Any]] = []
    used_ids: set[str] = set()
    consumed_end_offsets: set[int] = set()

    for order, begin in enumerate(REGION_BEGIN.finditer(proof_body), 1):
        marker_attributes = _parse_attributes(begin.group(1))
        nearby_attributes = _nearby_contract_attributes(proof_body, begin.start())
        attributes = {**nearby_attributes, **marker_attributes}
        admit_id = marker_attributes.get("admit_id", "")
        owner = marker_attributes.get("owner", "")

        matched_end: re.Match[str] | None = None
        for candidate in REGION_END.finditer(proof_body, begin.end()):
            if candidate.start() in consumed_end_offsets:
                continue
            end_id = _parse_attributes(candidate.group(1)).get("admit_id")
            if not end_id or not admit_id or end_id == admit_id:
                matched_end = candidate
                break

        if matched_end is None:
            issues.append(f"proof_region #{order} has no matching end marker")
            region_end = begin.end()
            end_id = ""
        else:
            consumed_end_offsets.add(matched_end.start())
            region_end = matched_end.end()
            end_id = _parse_attributes(matched_end.group(1)).get("admit_id", "")

        region_text = proof_body[begin.start() : region_end]
        masked_region = masked_body[begin.start() : region_end]
        tactic_admits = list(ADMIT_TACTIC.finditer(masked_region))
        admitted_commands = list(ADMITTED_COMMAND.finditer(masked_region))
        pending_count = len(tactic_admits) + len(admitted_commands)
        target = marker_attributes.get("target", "")
        kind = marker_attributes.get("kind", "")
        layer = attributes.get("layer", "")
        missing_fields = [field for field in REQUIRED_CONTRACT_FIELDS if not attributes.get(field)]

        if owner != "lemma":
            issues.append(f"proof_region #{order} must use owner: lemma")
        if not admit_id:
            issues.append(f"proof_region #{order} has no admit_id")
        elif admit_id in used_ids:
            issues.append(f"duplicate admit_id: {admit_id}")
        else:
            used_ids.add(admit_id)
        if end_id and admit_id and end_id != admit_id:
            issues.append(f"proof_region {admit_id} end marker uses admit_id {end_id}")
        if marker_attributes.get("theorem") not in (None, "", theorem_name):
            issues.append(f"proof_region {admit_id or order} names a different theorem")
        if kind not in LEAF_KINDS:
            issues.append(f"proof_region {admit_id or order} has non-leaf or unknown kind: {kind or '<missing>'}")
        if layer.lower() in {"paper", "theorem_spine", "theorem-spine"}:
            issues.append(f"proof_region {admit_id or order} is still a theorem-level planning node")
        if not target:
            issues.append(f"proof_region {admit_id or order} has no target")
        elif not re.search(rf"\b{re.escape(target)}\b", region_text[begin.end() - begin.start() :]):
            issues.append(f"proof_region {admit_id or order} does not wrap its target `{target}`")
        if missing_fields:
            issues.append(
                f"proof_region {admit_id or order} is missing contract fields: {', '.join(missing_fields)}"
            )
        if pending_count > 1:
            issues.append(f"proof_region {admit_id or order} contains {pending_count} pending proof holes; expected at most one")

        regions.append(
            {
                "order": order,
                "admit_id": admit_id,
                "owner": owner,
                "theorem": marker_attributes.get("theorem") or theorem_name,
                "kind": kind,
                "target": target,
                "plan_node": attributes.get("plan_node", ""),
                "depends_on": attributes.get("depends_on", ""),
                "source": attributes.get("source", ""),
                "input": attributes.get("input", ""),
                "output": attributes.get("output", ""),
                "layer": layer,
                "expected": attributes.get("expected", ""),
                "normal_form": attributes.get("normal_form", ""),
                "evidence": attributes.get("evidence", ""),
                "pending_count": pending_count,
                "start_offset": begin.start(),
                "end_offset": region_end,
            }
        )

    tactic_admits = list(ADMIT_TACTIC.finditer(masked_body))
    admitted_commands = list(ADMITTED_COMMAND.finditer(masked_body))
    terminators = list(PROOF_TERMINATOR.finditer(masked_body))
    final_terminator = terminators[-1].group(1) if terminators else None

    def inside_region(offset: int) -> bool:
        return any(region["start_offset"] <= offset < region["end_offset"] for region in regions)

    outside_tactic_admits = [match.start() for match in tactic_admits if not inside_region(match.start())]
    if outside_tactic_admits:
        issues.append(f"{len(outside_tactic_admits)} tactic admit(s) occur outside lemma-owned proof_regions")

    nonterminal_admitted = [
        match.start()
        for match in admitted_commands
        if not (terminators and match.start() == terminators[-1].start()) and not inside_region(match.start())
    ]
    if nonterminal_admitted:
        issues.append(f"{len(nonterminal_admitted)} nonterminal Admitted command(s) occur outside proof_regions")

    pending_leaf_count = sum(int(region["pending_count"]) for region in regions)
    if not regions:
        issues.append("no proof_region owner: lemma leaves were produced")
    if pending_leaf_count == 0:
        issues.append("no pending leaf obligation was preserved in the decomposition")
    if pending_leaf_count > 0 and final_terminator != "Admitted":
        issues.append("a skeleton with pending leaves must end the target theorem with Admitted.")
    if re.search(r"\bAbort\s*\.", masked_body):
        issues.append("Abort. is not permitted in a decomposition artifact")
    disallowed = sorted(set(DISALLOWED_DECLARATION.findall(masked_body)))
    if disallowed:
        issues.append(f"disallowed proof-body declaration(s): {', '.join(disallowed)}")

    for region in regions:
        region.pop("start_offset", None)
        region.pop("end_offset", None)

    return {
        "theorem": theorem_name,
        "region_count": len(regions),
        "pending_leaf_count": pending_leaf_count,
        "tactic_admit_count": len(tactic_admits),
        "admitted_command_count": len(admitted_commands),
        "final_terminator": final_terminator,
        "regions": regions,
        "issues": issues,
    }


def _coqc_timeout_seconds() -> int:
    raw = os.environ.get("OPENCODE_DECOMPOSE_COQC_TIMEOUT_SECONDS", "300")
    try:
        parsed = int(raw)
    except ValueError:
        return 300
    return parsed if parsed > 0 else 300


def compile_skeleton(workspace_dir: Path, theorem_file: Path) -> dict[str, Any]:
    command = ["coqc", theorem_file.name]
    started = datetime.now(timezone.utc)
    try:
        result = subprocess.run(
            command,
            cwd=str(workspace_dir),
            env=base.workspace_coq_environment(workspace_dir),
            capture_output=True,
            text=True,
            timeout=_coqc_timeout_seconds(),
        )
        return {
            "command": command,
            "exit_code": result.returncode,
            "ok": result.returncode == 0,
            "stdout": result.stdout,
            "stderr": result.stderr,
            "elapsed_seconds": round((datetime.now(timezone.utc) - started).total_seconds(), 3),
        }
    except subprocess.TimeoutExpired as exc:
        return {
            "command": command,
            "exit_code": None,
            "ok": False,
            "stdout": exc.stdout or "",
            "stderr": exc.stderr or "",
            "error": f"coqc timed out after {_coqc_timeout_seconds()} seconds",
            "elapsed_seconds": round((datetime.now(timezone.utc) - started).total_seconds(), 3),
        }
    except Exception as exc:
        return {
            "command": command,
            "exit_code": None,
            "ok": False,
            "stdout": "",
            "stderr": "",
            "error": f"{type(exc).__name__}: {exc}",
            "elapsed_seconds": round((datetime.now(timezone.utc) - started).total_seconds(), 3),
        }


def check_decomposition_success(
    source_theorem_file: Path,
    workspace_dir: Path,
    theorem_file: Path,
) -> tuple[bool, dict[str, Any]]:
    info: dict[str, Any] = {
        "completion_mode": COMPLETION_MODE,
        "proof_verified": False,
        "decomposition_verified": False,
    }
    integrity = base.inspect_theorem_edit_integrity(source_theorem_file, theorem_file)
    info.update(integrity)
    if integrity.get("unauthorized_modification") or integrity.get("integrity_check_failed"):
        return False, info

    try:
        structure = analyze_decomposition_structure(source_theorem_file, theorem_file)
    except Exception as exc:
        info["decomposition_issues"] = [f"{type(exc).__name__}: {exc}"]
        info["compile_error"] = info["decomposition_issues"][0]
        return False, info

    compile_result = compile_skeleton(workspace_dir, theorem_file)
    issues = list(structure["issues"])
    if not compile_result["ok"]:
        compiler_message = (
            compile_result.get("error")
            or compile_result.get("stderr")
            or compile_result.get("stdout")
            or "coqc failed without diagnostics"
        )
        issues.append(f"skeleton compilation failed: {str(compiler_message).strip()[:4000]}")

    decomposition_checkpoint = base.extract_latest_decomposition_checkpoint(
        workspace_dir.parent / "opencode_events.jsonl"
    )
    current_source_hash = sha256_file(theorem_file)
    if decomposition_checkpoint is None:
        issues.append("no source-bound decomposition checkpoint receipt was emitted by coqc/checkpoint")
    elif decomposition_checkpoint.get("source_hash") != current_source_hash:
        issues.append("the latest decomposition checkpoint receipt belongs to a different theorem source revision")
    elif not (
        decomposition_checkpoint.get("status") == "ready"
        and decomposition_checkpoint.get("terminal_ready") is True
        and decomposition_checkpoint.get("materialization_complete") is True
    ):
        blockers = decomposition_checkpoint.get("blockers")
        detail = "; ".join(str(item) for item in blockers) if isinstance(blockers, list) else ""
        issues.append(
            "latest source-bound decomposition checkpoint is not ready"
            + (f": {detail}" if detail else "")
        )

    info.update(
        {
            "has_qed": structure["final_terminator"] == "Qed",
            "has_admitted": structure["admitted_command_count"] > 0,
            "has_admit": structure["tactic_admit_count"] > 0,
            "proof_region_count": structure["region_count"],
            "pending_leaf_count": structure["pending_leaf_count"],
            "admit_ids": [region["admit_id"] for region in structure["regions"]],
            "decomposition_manifest": structure["regions"],
            "decomposition_issues": issues,
            "skeleton_compile_ok": bool(compile_result["ok"]),
            "coqc_command": compile_result["command"],
            "coqc_exit_code": compile_result["exit_code"],
            "coqc_elapsed_seconds": compile_result["elapsed_seconds"],
            "coqc_stdout": str(compile_result.get("stdout", ""))[:4000],
            "coqc_stderr": str(compile_result.get("stderr", ""))[:4000],
            "decomposition_checkpoint": decomposition_checkpoint,
        }
    )
    if issues:
        info["compile_error"] = "\n".join(issues)[:8000]
        return False, info

    info["decomposition_verified"] = True
    info.pop("compile_error", None)
    return True, info


def build_prompt(
    theorem_file: Path,
    theorem_name: str,
    theorem_statement: str,
    *,
    enable_skill: bool = False,
    segmented_proof_workflow: bool = False,
) -> str:
    del segmented_proof_workflow
    skill_note = (
        "Workspace-local skills are available, but use them only to understand a directly relevant decomposition boundary.\n"
        if enable_skill
        else ""
    )
    return f"""## Phase-1 Decomposition Experiment

Work only on `{theorem_file.name}` and the target theorem `{theorem_name}`. This is a decomposition-only run: write and freeze the theorem-level semantic/shape skeleton, then stop. Never call a lemma proof agent and never discharge a frozen leaf.

The target declaration and statement must remain unchanged:

```coq
{theorem_statement}
```

Completion contract:

1. Read `proof.tex` first when it exists, then read the target theorem and only directly relevant workspace facts.
2. Write the complete parent composition and isolate each smallest unresolved local leaf in one `proof_region owner: lemma` with a stable `admit_id` and all required contract fields.
3. Keep exactly one pending `admit.` in each unresolved leaf region. Do not place an admit in a parent claim, final bridge, or outside a leaf region.
4. Keep the target theorem unfinished with `Admitted.` while leaves remain. Do not replace it with `Qed.` and do not prove inside the frozen regions.
5. Run `coqc {theorem_file.name}` and repair only skeleton syntax, typing, target shapes, parent composition, or region contracts until the complete file compiles with the leaf admits retained.
6. Return a concise decomposition manifest and stop immediately. The experiment runner independently recompiles the file after you return.
7. Use the runner's exact machine-readable marker syntax for every leaf. The markers are Coq comments, NOT tactics and NOT bare lines:
   `(* proof_region begin owner: lemma admit_id: <stable_id> theorem: <theorem_name> kind: <leaf_kind> target: <local_target_name> plan_node: <node> depends_on: <...> source: <...> input: <...> output: <...> layer: <semantic|shape> expected: <...> normal_form: "<coq goal shape>" evidence: <...> *)`
   Place this begin comment immediately before the exported local target statement, and place `(* proof_region end admit_id: <stable_id> *)` immediately after that target's complete `{{ ... }}` proof block. Keep every contract field inline in the begin comment; quote any value containing spaces with double quotes. Do not use `Tactic Notation`, bare `proof_region begin.` / `proof_region end.`, or markers nested inside larger decorative comments.

Do not add `Abort`, `Axiom`, `Hypothesis`, `Parameter`, or `Variable`; do not change text outside the permitted target proof body except a strictly necessary additive import. {skill_note}"""


def build_continuation_prompt(
    theorem_file: Path,
    theorem_name: str,
    theorem_statement: str,
    *,
    proof_info: dict | None = None,
    retry_index: int,
    max_retries: int,
    enable_skill: bool = False,
    segmented_proof_workflow: bool = False,
    history_compaction: str = "",
) -> str:
    del theorem_statement, enable_skill, segmented_proof_workflow, history_compaction
    diagnostics = base._trim_compile_error((proof_info or {}).get("compile_error"))
    diagnostic_section = f"\nThe runner found these blockers:\n\n```text\n{diagnostics}\n```\n" if diagnostics else ""
    return f"""## Continue Phase-1 Skeleton Repair

The previous decomposition attempt for `{theorem_name}` in `{theorem_file.name}` is not yet an accepted artifact (retry {retry_index} of {max_retries}).{diagnostic_section}

Repair only the decomposition skeleton and its contract metadata. Preserve every valid `proof_region`, stable `admit_id`, and leaf `admit.`. Do not prove a leaf, call a lemma agent, enter Phase 2, or replace the final `Admitted.` with `Qed.`. Ensure all admits are inside smallest single-contract lemma-owned regions, parent composition is explicit, and `coqc {theorem_file.name}` succeeds with those admits retained.

The runner's region gate recognizes ONLY these exact Coq comment markers (not tactics, not bare lines, not decorative comment blocks):
   `(* proof_region begin owner: lemma admit_id: <id> theorem: <theorem> kind: <leaf_kind> target: <target> plan_node: <node> depends_on: <...> source: <...> input: <...> output: <...> layer: <semantic|shape> expected: <...> normal_form: "<coq shape>" evidence: <...> *)`
   `(* proof_region end admit_id: <id> *)`
Place the begin comment immediately before the exported local target statement, and the end comment immediately after its complete `{{ ... }}` proof block. Keep all contract fields inline in the begin comment; quote any value containing spaces. Keep exactly one pending `admit.` inside each leaf region and no admits outside regions. Then report the manifest and stop."""


def _workspace_target_v_file(workspace_dir: Path) -> Path | None:
    candidates = sorted(
        path
        for path in workspace_dir.glob("*.v")
        if path.is_file()
        and not path.name.startswith("agent_request")
        and not path.name.endswith("_cp_aux.v")
        and not path.name.startswith(".")
        and path.name != "final.v"
    )
    return candidates[0] if candidates else None


def _invoke_decompose(
    cmd: list[str],
    *,
    env: dict[str, str],
    workspace_dir: Path,
    log_file: Path,
    json_log: Path,
    timeout_seconds: int,
    model_response_timeout_seconds: int = base.MODEL_RESPONSE_TIMEOUT_SECONDS,
    max_total_tokens: int | None = None,
    baseline_tokens: int = 0,
) -> tuple[int | None, bool, int | None, bool, bool]:
    next_cmd = list(cmd)
    if len(next_cmd) >= 2 and next_cmd[1] == "run":
        prompt = next_cmd[-1]
        prefix = next_cmd[:-1]
        additions: list[str] = []
        if "--agent" not in prefix:
            additions.extend(["--agent", "prover"])
        if "--file" not in prefix:
            target = _workspace_target_v_file(workspace_dir)
            if target is not None:
                additions.extend(["--file", target.name])
        next_cmd = [*prefix, *additions, "--", prompt]

    return ORIGINAL_INVOKE_OPENCODE(
        next_cmd,
        env=env,
        workspace_dir=workspace_dir,
        log_file=log_file,
        json_log=json_log,
        timeout_seconds=timeout_seconds,
        model_response_timeout_seconds=model_response_timeout_seconds,
        max_total_tokens=max_total_tokens,
        baseline_tokens=baseline_tokens,
    )


def _atomic_copy(source: Path, destination: Path) -> None:
    destination.parent.mkdir(parents=True, exist_ok=True)
    descriptor, temporary = tempfile.mkstemp(prefix=f".{destination.name}.", suffix=".tmp", dir=destination.parent)
    temporary_path = Path(temporary)
    try:
        with os.fdopen(descriptor, "wb") as output, source.open("rb") as input_stream:
            shutil.copyfileobj(input_stream, output)
            output.flush()
            os.fsync(output.fileno())
        os.replace(temporary_path, destination)
    finally:
        temporary_path.unlink(missing_ok=True)


def _summarize_event_trace(path: Path) -> dict[str, Any]:
    event_counts: Counter[str] = Counter()
    tool_counts: Counter[str] = Counter()
    sessions: set[str] = set()
    total_tokens = 0
    valid_lines = 0
    invalid_lines = 0
    first_timestamp: Any = None
    last_timestamp: Any = None

    try:
        stream = path.open("r", encoding="utf-8", errors="ignore")
    except FileNotFoundError:
        return {"path": path.name, "exists": False, "line_count": 0}

    with stream:
        for raw_line in stream:
            if not raw_line.strip():
                continue
            try:
                event = json.loads(raw_line)
            except json.JSONDecodeError:
                invalid_lines += 1
                continue
            if not isinstance(event, dict):
                invalid_lines += 1
                continue
            valid_lines += 1
            event_type = str(event.get("type", "unknown"))
            event_counts[event_type] += 1
            timestamp = event.get("timestamp")
            if first_timestamp is None:
                first_timestamp = timestamp
            last_timestamp = timestamp
            session_id = event.get("sessionID")
            if isinstance(session_id, str):
                sessions.add(session_id)
            part = event.get("part") if isinstance(event.get("part"), dict) else {}
            if event_type == "tool_use" and isinstance(part.get("tool"), str):
                tool_counts[part["tool"]] += 1
            if event_type == "step_finish":
                tokens = part.get("tokens") if isinstance(part.get("tokens"), dict) else {}
                step_total = tokens.get("total")
                if isinstance(step_total, (int, float)):
                    total_tokens += int(step_total)
                else:
                    total_tokens += sum(
                        int(tokens.get(key, 0))
                        for key in ("input", "output", "reasoning")
                        if isinstance(tokens.get(key, 0), (int, float))
                    )

    return {
        "path": path.name,
        "exists": True,
        "line_count": valid_lines + invalid_lines,
        "valid_json_lines": valid_lines,
        "invalid_json_lines": invalid_lines,
        "sha256": sha256_file(path),
        "size_bytes": path.stat().st_size,
        "first_timestamp": first_timestamp,
        "last_timestamp": last_timestamp,
        "sessions": sorted(sessions),
        "event_counts": dict(sorted(event_counts.items())),
        "tool_counts": dict(sorted(tool_counts.items())),
        "total_tokens": total_tokens,
    }


def _summarize_request_traces(run_dir: Path) -> dict[str, Any]:
    root = run_dir / "request_traces"
    request_files = sorted(root.rglob("requests.jsonl")) if root.is_dir() else []
    summaries: list[dict[str, Any]] = []
    total_records = 0
    for path in request_files:
        records = 0
        with path.open("r", encoding="utf-8", errors="ignore") as stream:
            for line in stream:
                if line.strip():
                    records += 1
        total_records += records
        summaries.append(
            {
                "path": str(path.relative_to(run_dir)),
                "records": records,
                "size_bytes": path.stat().st_size,
                "sha256": sha256_file(path),
            }
        )
    native_summaries = sorted(
        str(path.relative_to(run_dir))
        for path in root.rglob("summary.json")
    ) if root.is_dir() else []
    return {
        "root": "request_traces",
        "exists": root.is_dir(),
        "request_files": summaries,
        "request_file_count": len(summaries),
        "request_record_count": total_records,
        "native_summary_files": native_summaries,
    }


def _write_compile_log(path: Path, compile_info: dict[str, Any]) -> None:
    command = " ".join(str(item) for item in compile_info.get("coqc_command", []))
    text = (
        f"command: {command}\n"
        f"exit_code: {compile_info.get('coqc_exit_code')}\n"
        f"elapsed_seconds: {compile_info.get('coqc_elapsed_seconds')}\n"
        f"skeleton_compile_ok: {compile_info.get('skeleton_compile_ok')}\n\n"
        "--- stdout ---\n"
        f"{compile_info.get('coqc_stdout', '')}\n\n"
        "--- stderr ---\n"
        f"{compile_info.get('coqc_stderr', '')}\n"
    )
    base.write_text(path, text)


def finalize_decomposition_artifacts(
    summary: dict[str, Any],
    *,
    run_dir: Path,
    progress_file: Path,
) -> dict[str, Any]:
    workspace_dir = Path(str(summary["runtime_workspace_dir"]))
    theorem_file = workspace_dir / str(summary["theorem_file"])
    source_theorem_file = Path(str(summary["source_theorem_file"]))

    verified, final_info = check_decomposition_success(source_theorem_file, workspace_dir, theorem_file)
    final_snapshot = run_dir / "final.v"
    if theorem_file.is_file():
        _atomic_copy(theorem_file, final_snapshot)

    manifest = {
        "schema_version": 1,
        "completion_mode": COMPLETION_MODE,
        "generated_at": now_iso(),
        "workspace": summary.get("workspace"),
        "theorem": summary.get("theorem_name"),
        "source_filename": theorem_file.name,
        "final_snapshot": final_snapshot.name if final_snapshot.is_file() else None,
        "final_snapshot_sha256": sha256_file(final_snapshot) if final_snapshot.is_file() else None,
        "decomposition_verified": verified,
        "skeleton_compile_ok": final_info.get("skeleton_compile_ok", False),
        "proof_region_count": final_info.get("proof_region_count", 0),
        "pending_leaf_count": final_info.get("pending_leaf_count", 0),
        "admit_ids": final_info.get("admit_ids", []),
        "regions": final_info.get("decomposition_manifest", []),
        "issues": final_info.get("decomposition_issues", []),
    }
    manifest_path = run_dir / "decomposition_manifest.json"
    base.write_json(manifest_path, manifest)

    compile_log = run_dir / "compile.log"
    _write_compile_log(compile_log, final_info)

    event_trace = _summarize_event_trace(run_dir / "opencode_events.jsonl")
    request_trace = _summarize_request_traces(run_dir)
    trace_summary = {
        "schema_version": 1,
        "completion_mode": COMPLETION_MODE,
        "generated_at": now_iso(),
        "workspace": summary.get("workspace"),
        "theorem": summary.get("theorem_name"),
        "event_trace": event_trace,
        "request_trace": request_trace,
        "artifacts": {
            "final_snapshot": final_snapshot.name if final_snapshot.is_file() else None,
            "final_snapshot_sha256": sha256_file(final_snapshot) if final_snapshot.is_file() else None,
            "decomposition_manifest": manifest_path.name,
            "compile_log": compile_log.name,
        },
        "decomposition_verified": verified,
        "skeleton_compile_ok": final_info.get("skeleton_compile_ok", False),
    }
    trace_summary_path = run_dir / "trace_summary.json"
    base.write_json(trace_summary_path, trace_summary)

    previous_status = summary.get("status")
    summary.update(final_info)
    summary.update(
        {
            "completion_mode": COMPLETION_MODE,
            "final_snapshot": final_snapshot.name if final_snapshot.is_file() else None,
            "final_snapshot_sha256": sha256_file(final_snapshot) if final_snapshot.is_file() else None,
            "event_trace": "opencode_events.jsonl",
            "event_trace_sha256": event_trace.get("sha256"),
            "trace_summary": trace_summary_path.name,
            "decomposition_manifest_file": manifest_path.name,
            "compile_log": compile_log.name,
            "artifact_finalized_at": now_iso(),
        }
    )
    if verified:
        summary["status"] = "success"
        if previous_status != "success":
            summary["status_before_artifact_validation"] = previous_status
    elif previous_status == "success":
        summary["status"] = "artifact_validation_error"

    base.write_json(run_dir / "result.json", summary)
    base.append_jsonl(
        progress_file,
        {
            "event": "decomposition_artifacts_finalized",
            "workspace": summary.get("workspace"),
            "status": summary.get("status"),
            "decomposition_verified": verified,
            "skeleton_compile_ok": final_info.get("skeleton_compile_ok", False),
            "final_snapshot": str(final_snapshot),
            "trace_summary": str(trace_summary_path),
        },
    )
    return summary


def run_workspace(*args: Any, **kwargs: Any) -> dict[str, Any]:
    base_run_dir = Path(args[0] if args else kwargs["base_run_dir"])
    workspace_name = str(args[1] if len(args) > 1 else kwargs["workspace_name"])
    progress_file = Path(args[2] if len(args) > 2 else kwargs["progress_file"])
    run_dir = base_run_dir / workspace_name
    extra_env = dict(kwargs.get("extra_env") or {})
    extra_env["OPENCODE_PROOF_WORKFLOW_MODE"] = COMPLETION_MODE
    with tempfile.TemporaryDirectory(prefix=f"prosabuddy-decompose-{workspace_name}-") as runtime_data:
        extra_env["OPENCODE_RUNTIME_DATA_HOME"] = runtime_data
        kwargs["extra_env"] = extra_env
        summary = ORIGINAL_RUN_WORKSPACE(*args, **kwargs)
        try:
            return finalize_decomposition_artifacts(summary, run_dir=run_dir, progress_file=progress_file)
        except Exception as exc:
            summary["completion_mode"] = COMPLETION_MODE
            summary["artifact_error"] = f"{type(exc).__name__}: {exc}"
            if summary.get("status") == "success":
                summary["status"] = "artifact_validation_error"
            base.write_json(run_dir / "result.json", summary)
            return summary


def _write_json_with_mode(path: Path, payload: object) -> None:
    if path.name == "config.json" and isinstance(payload, dict):
        payload = {**payload, "completion_mode": COMPLETION_MODE, "artifact_schema_version": 1}
    ORIGINAL_WRITE_JSON(path, payload)


def main() -> int:
    originals = {
        "build_prompt": base.build_prompt,
        "build_continuation_prompt": base.build_continuation_prompt,
        "check_proof_success": base.check_proof_success,
        "invoke": base._invoke_opencode,
        "run_workspace": base.run_workspace,
        "write_json": base.write_json,
        "record_runner": base.DEFAULT_RECORD_RUNNER,
    }
    try:
        base.build_prompt = build_prompt
        base.build_continuation_prompt = build_continuation_prompt
        base.check_proof_success = check_decomposition_success
        base._invoke_opencode = _invoke_decompose
        base.run_workspace = run_workspace
        base.write_json = _write_json_with_mode
        base.DEFAULT_RECORD_RUNNER = "run_casestudy_decompose.py"
        return base.main()
    finally:
        base.build_prompt = originals["build_prompt"]
        base.build_continuation_prompt = originals["build_continuation_prompt"]
        base.check_proof_success = originals["check_proof_success"]
        base._invoke_opencode = originals["invoke"]
        base.run_workspace = originals["run_workspace"]
        base.write_json = originals["write_json"]
        base.DEFAULT_RECORD_RUNNER = originals["record_runner"]


if __name__ == "__main__":
    try:
        if base.maybe_nohup(EXPERIMENT_ROOT, Path(__file__).resolve(), sys.argv[1:]):
            raise SystemExit(0)
        raise SystemExit(main())
    except KeyboardInterrupt:
        raise SystemExit(130)
