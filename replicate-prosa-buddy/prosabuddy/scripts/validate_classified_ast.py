#!/usr/bin/env python3
"""Validate two Rocq 9.1 classified astdump JSONL files.

The classifier output is expected to be produced by classify_vernac_ast.ml.
The validator is deliberately fail-closed: missing ASTs, classifications, plugin
metadata, or malformed proof boundaries cause rejection.

This script enforces source/AST policy only.  Kernel-type comparison,
Print Assumptions, typing-flag checks, coqc, and coqchk remain separate semantic
checks and are not replaced by this validator.
"""

from __future__ import annotations

import argparse
import json
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterable, Sequence


VALID_PHASES = {"VernacSynterp", "VernacSynPure"}
VALID_CATEGORIES = {
    "StartProof",
    "Sideff",
    "Qed",
    "ProofStep",
    "Query",
    "ProofMode",
    "Meta",
}

# Ltac proof commands are emitted by Rocq's own runtime plugin. An original
# exercise may have an empty/Admitted proof and therefore contain no extension
# node from which this plugin could be learned. Trust this one exact built-in
# identity by default; all other newly observed plugins remain fail-closed.
BUILTIN_TRUSTED_PLUGINS = frozenset({"rocq-runtime.plugins.ltac"})


@dataclass(frozen=True)
class Reason:
    code: str
    message: str
    file: str | None = None
    index: int | None = None
    line: int | None = None
    details: dict[str, Any] | None = None

    def as_json(self) -> dict[str, Any]:
        result: dict[str, Any] = {"code": self.code, "message": self.message}
        if self.file is not None:
            result["file"] = self.file
        if self.index is not None:
            result["index"] = self.index
        if self.line is not None:
            result["line"] = self.line
        if self.details:
            result["details"] = self.details
        return result


@dataclass(frozen=True)
class Command:
    file: str
    position: int
    record: dict[str, Any]
    normalized_ast: Any

    @property
    def index(self) -> int:
        value = self.record.get("index")
        return value if isinstance(value, int) else self.position + 1

    @property
    def line(self) -> int | None:
        value = self.record.get("source_line")
        return value if isinstance(value, int) else None

    @property
    def phase(self) -> str:
        return self.record["phase"]

    @property
    def kind(self) -> str:
        return self.record["vernac_kind"]

    @property
    def category(self) -> str:
        return self.record["category"]

    @property
    def names(self) -> tuple[str, ...]:
        return tuple(self.record.get("names", []))

    def reason(
        self,
        code: str,
        message: str,
        *,
        details: dict[str, Any] | None = None,
    ) -> Reason:
        return Reason(
            code=code,
            message=message,
            file=self.file,
            index=self.index,
            line=self.line,
            details=details,
        )

    def comparison_key(self) -> Any:
        """Fields that must remain stable outside the selected proof body."""
        return (
            self.normalized_ast,
            self.phase,
            self.kind,
            self.category,
            self.names,
            self.record.get("when"),
            self.record.get("opacity_guarantee"),
            self.record.get("qed_action"),
            self.record.get("proof_block_detection"),
            _freeze(self.record.get("controls")),
            _freeze(self.record.get("attributes")),
            _freeze(self.record.get("require")),
            _freeze(self.record.get("extension")),
            _freeze(self.record.get("proof_end")),
        )


@dataclass(frozen=True)
class ProofInterval:
    ordinal: int
    start: int
    end: int
    names: tuple[str, ...]


@dataclass(frozen=True)
class Policy:
    stage: str
    target: str | None
    allowed_requires: frozenset[str]
    allowed_require_modes: frozenset[str]
    additional_trusted_plugins: frozenset[str]
    trust_original_plugins: bool
    allow_queries: bool
    allow_attributes_in_proof: bool


def _freeze(value: Any) -> Any:
    if isinstance(value, dict):
        return tuple(sorted((key, _freeze(item)) for key, item in value.items()))
    if isinstance(value, list):
        return tuple(_freeze(item) for item in value)
    return value


_DROP_LOCATION = object()


def _normalize_ast(value: Any) -> Any:
    # Most CAst locations are JSON object fields named "loc".  Generic plugin
    # arguments produced by serlib encode records as association-list-shaped
    # arrays, where a location appears as ["loc", ...].
    if isinstance(value, list) and len(value) == 2 and value[0] == "loc":
        return _DROP_LOCATION
    if isinstance(value, dict):
        return tuple(
            sorted(
                (key, normalized)
                for key, item in value.items()
                if key != "loc"
                for normalized in [_normalize_ast(item)]
                if normalized is not _DROP_LOCATION
            )
        )
    if isinstance(value, list):
        normalized_items = (_normalize_ast(item) for item in value)
        return tuple(item for item in normalized_items if item is not _DROP_LOCATION)
    return value


def normalize_ast(value: Any) -> Any:
    """Remove source locations while retaining every semantic AST field."""
    normalized = _normalize_ast(value)
    return () if normalized is _DROP_LOCATION else normalized


def load_commands(path: Path) -> tuple[list[Command], list[Reason]]:
    commands: list[Command] = []
    reasons: list[Reason] = []
    schema_mismatch_count = 0
    schema_mismatch_first_index: int | None = None
    schema_mismatch_first_line: int | None = None
    schema_missing_fields: set[str] = set()
    try:
        handle = path.open("r", encoding="utf-8")
    except OSError as exc:
        return [], [Reason("INPUT_OPEN_FAILED", f"无法读取输入文件：{exc}", file=str(path))]

    with handle:
        for line_number, text in enumerate(handle, 1):
            if not text.strip():
                continue
            try:
                record = json.loads(text)
            except json.JSONDecodeError as exc:
                reasons.append(
                    Reason(
                        "INVALID_JSON",
                        f"第 {line_number} 个 JSONL 记录不是合法 JSON：{exc.msg}",
                        file=str(path),
                        line=line_number,
                    )
                )
                continue
            if not isinstance(record, dict):
                reasons.append(
                    Reason(
                        "INVALID_RECORD",
                        "分类 AST 的每一行必须是 JSON object。",
                        file=str(path),
                        line=line_number,
                    )
                )
                continue
            if "error" in record:
                reasons.append(
                    Reason(
                        "CLASSIFIER_ERROR",
                        f"分类器报告错误：{record.get('error')}",
                        file=str(path),
                        index=record.get("index") if isinstance(record.get("index"), int) else None,
                        line=record.get("source_line") if isinstance(record.get("source_line"), int) else line_number,
                    )
                )
                continue

            missing = [
                field
                for field in (
                    "phase",
                    "vernac_kind",
                    "category",
                    "names",
                    "controls",
                    "attributes",
                    "require",
                    "extension",
                    "proof_end",
                    "ast",
                )
                if field not in record
            ]
            if missing:
                schema_mismatch_count += 1
                schema_missing_fields.update(missing)
                if schema_mismatch_first_line is None:
                    schema_mismatch_first_index = (
                        record.get("index") if isinstance(record.get("index"), int) else None
                    )
                    schema_mismatch_first_line = (
                        record.get("source_line")
                        if isinstance(record.get("source_line"), int)
                        else line_number
                    )
                continue

            phase = record.get("phase")
            category = record.get("category")
            if phase not in VALID_PHASES:
                reasons.append(
                    Reason(
                        "UNKNOWN_PHASE",
                        f"未知 AST phase：{phase!r}。",
                        file=str(path),
                        index=record.get("index") if isinstance(record.get("index"), int) else None,
                        line=record.get("source_line") if isinstance(record.get("source_line"), int) else line_number,
                    )
                )
                continue
            if category not in VALID_CATEGORIES:
                reasons.append(
                    Reason(
                        "UNKNOWN_CLASSIFICATION",
                        f"未知 vernacular classification：{category!r}。",
                        file=str(path),
                        index=record.get("index") if isinstance(record.get("index"), int) else None,
                        line=record.get("source_line") if isinstance(record.get("source_line"), int) else line_number,
                    )
                )
                continue
            if not isinstance(record.get("names"), list):
                reasons.append(
                    Reason(
                        "INVALID_NAMES",
                        "names 字段必须是数组。",
                        file=str(path),
                        index=record.get("index") if isinstance(record.get("index"), int) else None,
                        line=record.get("source_line") if isinstance(record.get("source_line"), int) else line_number,
                    )
                )
                continue
            commands.append(
                Command(
                    file=str(path),
                    position=len(commands),
                    record=record,
                    normalized_ast=normalize_ast(record["ast"]),
                )
            )
    if schema_mismatch_count:
        reasons.append(
            Reason(
                "CLASSIFIED_AST_SCHEMA_MISMATCH",
                "分类记录缺少策略检查需要的字段。请使用配套的 classify_vernac_ast.ml 重新生成。",
                file=str(path),
                index=schema_mismatch_first_index,
                line=schema_mismatch_first_line,
                details={
                    "affected_records": schema_mismatch_count,
                    "missing_fields": sorted(schema_missing_fields),
                },
            )
        )
    if not commands and not reasons:
        reasons.append(Reason("EMPTY_INPUT", "分类 AST 文件为空。", file=str(path)))
    return commands, reasons


def build_proof_intervals(
    commands: Sequence[Command], label: str
) -> tuple[list[ProofInterval], list[Reason]]:
    stack: list[tuple[int, tuple[str, ...]]] = []
    intervals: list[ProofInterval] = []
    reasons: list[Reason] = []
    for position, command in enumerate(commands):
        if command.category == "StartProof":
            stack.append((position, command.names))
        elif command.category == "Qed":
            if not stack:
                reasons.append(
                    command.reason(
                        "UNMATCHED_PROOF_END",
                        f"{label}中存在没有对应 StartProof 的证明结束节点。",
                    )
                )
                continue
            start, names = stack.pop()
            intervals.append(ProofInterval(-1, start, position, names))
    for start, names in stack:
        reasons.append(
            commands[start].reason(
                "UNCLOSED_PROOF",
                f"{label}中的证明没有对应的 Qed/Admitted/Abort 结束节点。",
                details={"names": list(names)},
            )
        )
    intervals.sort(key=lambda item: item.start)
    return [
        ProofInterval(ordinal, item.start, item.end, item.names)
        for ordinal, item in enumerate(intervals)
    ], reasons


def interval_key(commands: Sequence[Command], interval: ProofInterval) -> Any:
    return tuple(
        commands[position].comparison_key()
        for position in range(interval.start, interval.end + 1)
    )


def select_target(
    original: Sequence[Command],
    candidate: Sequence[Command],
    original_proofs: Sequence[ProofInterval],
    candidate_proofs: Sequence[ProofInterval],
    requested_target: str | None,
) -> tuple[tuple[ProofInterval, ProofInterval] | None, list[Reason]]:
    reasons: list[Reason] = []
    if len(original_proofs) != len(candidate_proofs):
        reasons.append(
            Reason(
                "PROOF_COUNT_CHANGED",
                "候选文件改变了 StartProof/Qed 配对后的证明数量。",
                details={"original": len(original_proofs), "candidate": len(candidate_proofs)},
            )
        )
        return None, reasons

    for original_proof, candidate_proof in zip(original_proofs, candidate_proofs):
        if original_proof.names != candidate_proof.names:
            reasons.append(
                candidate[candidate_proof.start].reason(
                    "PROOF_IDENTITY_CHANGED",
                    "候选文件改变了证明声明的名称或顺序。",
                    details={
                        "original_names": list(original_proof.names),
                        "candidate_names": list(candidate_proof.names),
                        "proof_ordinal": original_proof.ordinal,
                    },
                )
            )
    if reasons:
        return None, reasons

    if requested_target is not None:
        matching = [
            proof
            for proof in original_proofs
            if requested_target in proof.names
        ]
        if len(matching) != 1:
            reasons.append(
                Reason(
                    "TARGET_NOT_UNIQUE",
                    "--target 必须在原始 AST 中唯一对应一个 StartProof。",
                    details={"target": requested_target, "matches": len(matching)},
                )
            )
            return None, reasons
        original_target = matching[0]
        candidate_target = candidate_proofs[original_target.ordinal]
    else:
        changed_ordinals = [
            original_proof.ordinal
            for original_proof, candidate_proof in zip(original_proofs, candidate_proofs)
            if interval_key(original, original_proof)
            != interval_key(candidate, candidate_proof)
        ]
        if len(changed_ordinals) == 1:
            ordinal = changed_ordinals[0]
            original_target = original_proofs[ordinal]
            candidate_target = candidate_proofs[ordinal]
        elif len(changed_ordinals) == 0 and len(original_proofs) == 1:
            original_target = original_proofs[0]
            candidate_target = candidate_proofs[0]
        elif len(changed_ordinals) == 0:
            reasons.append(
                Reason(
                    "TARGET_NOT_IDENTIFIED",
                    "多个证明均未发生 AST 变化，无法自动确定目标；请使用 --target。",
                )
            )
            return None, reasons
        else:
            reasons.append(
                Reason(
                    "MULTIPLE_PROOFS_CHANGED",
                    "候选文件修改了多个证明；策略只允许修改一个目标证明。",
                    details={"proof_ordinals": changed_ordinals},
                )
            )
            return None, reasons

    changed_other_proofs = [
        original_proof.ordinal
        for original_proof, candidate_proof in zip(original_proofs, candidate_proofs)
        if original_proof.ordinal != original_target.ordinal
        and interval_key(original, original_proof)
        != interval_key(candidate, candidate_proof)
    ]
    if changed_other_proofs:
        reasons.append(
            Reason(
                "NON_TARGET_PROOF_CHANGED",
                "候选文件修改了目标之外的证明。",
                details={"proof_ordinals": changed_other_proofs},
            )
        )
    return (original_target, candidate_target), reasons


def plugin_name(command: Command) -> str | None:
    extension = command.record.get("extension")
    if isinstance(extension, dict) and isinstance(extension.get("plugin"), str):
        return extension["plugin"]
    return None


def original_plugins(commands: Iterable[Command]) -> set[str]:
    return {
        plugin
        for command in commands
        if command.kind == "VernacExtend"
        for plugin in [plugin_name(command)]
        if plugin is not None
    }


def has_controls(command: Command) -> bool:
    controls = command.record.get("controls")
    return not isinstance(controls, list) or bool(controls)


def has_attributes(command: Command) -> bool:
    attributes = command.record.get("attributes")
    return not isinstance(attributes, list) or bool(attributes)


def validate_target_start(
    original: Sequence[Command],
    candidate: Sequence[Command],
    original_target: ProofInterval,
    candidate_target: ProofInterval,
) -> list[Reason]:
    original_start = original[original_target.start]
    candidate_start = candidate[candidate_target.start]
    if original_start.comparison_key() != candidate_start.comparison_key():
        return [
            candidate_start.reason(
                "TARGET_DECLARATION_CHANGED",
                "目标 theorem 的声明 AST、attributes、controls 或分类与原始文件不同。",
                details={
                    "original_names": list(original_target.names),
                    "candidate_names": list(candidate_target.names),
                },
            )
        ]
    return []


def validate_proof_body(
    commands: Sequence[Command],
    target: ProofInterval,
    policy: Policy,
    trusted_plugins: set[str],
) -> list[Reason]:
    reasons: list[Reason] = []
    proof_markers = 0
    for position in range(target.start + 1, target.end):
        command = commands[position]
        if has_controls(command):
            reasons.append(
                command.reason(
                    "PROOF_CONTROL_FORBIDDEN",
                    "目标 proof body 中不允许 Fail、Timeout、Redirect、Time 等 control wrapper。",
                    details={"controls": command.record.get("controls")},
                )
            )
        if has_attributes(command) and not policy.allow_attributes_in_proof:
            reasons.append(
                command.reason(
                    "PROOF_ATTRIBUTE_FORBIDDEN",
                    "目标 proof body 中不允许带 vernacular attributes 的命令。",
                    details={"attributes": command.record.get("attributes")},
                )
            )

        if command.phase == "VernacSynterp":
            if command.kind != "VernacExtend":
                reasons.append(
                    command.reason(
                        "PROOF_SYNTERP_FORBIDDEN",
                        "proof 内的 VernacSynterp 仅允许可信 VernacExtend proof step。",
                        details={"vernac_kind": command.kind, "category": command.category},
                    )
                )
                continue
            if command.category == "Query" and policy.allow_queries:
                pass
            elif command.category != "ProofStep":
                reasons.append(
                    command.reason(
                        "PROOF_EXTENSION_NOT_PROOF_STEP",
                        "VernacExtend 没有被官方分类器分类为 VtProofStep。",
                        details={"category": command.category},
                    )
                )
                continue
            plugin = plugin_name(command)
            if plugin is None:
                reasons.append(
                    command.reason(
                        "EXTENSION_METADATA_MISSING",
                        "VernacExtend 缺少插件身份，无法验证其是否可信。",
                    )
                )
            elif plugin not in trusted_plugins:
                reasons.append(
                    command.reason(
                        "UNTRUSTED_EXTENSION_PLUGIN",
                        "proof step 来自不在白名单中的插件。",
                        details={
                            "plugin": plugin,
                            "entry": (command.record.get("extension") or {}).get("entry"),
                        },
                    )
                )
            continue

        if command.phase != "VernacSynPure":
            reasons.append(command.reason("UNKNOWN_PHASE", "proof 内出现未知 AST phase。"))
            continue
        if command.category == "ProofStep":
            if command.kind == "VernacProof":
                proof_markers += 1
                if proof_markers > 1 or position != target.start + 1:
                    reasons.append(
                        command.reason(
                            "MISPLACED_PROOF_MARKER",
                            "VernacProof 最多出现一次，并且只能是目标声明后的第一条命令。",
                        )
                    )
            continue
        if command.category == "Query" and policy.allow_queries:
            continue
        if command.category == "Sideff":
            reasons.append(
                command.reason(
                    "PROOF_SIDE_EFFECT",
                    "目标 proof body 中出现 VtSideff；可能新增公理、定义、实例、hint 或修改全局状态。",
                    details={"vernac_kind": command.kind},
                )
            )
        elif command.category == "Query":
            reasons.append(
                command.reason(
                    "PROOF_QUERY_FORBIDDEN",
                    "严格策略不允许在最终 proof body 中保留查询命令。",
                    details={"vernac_kind": command.kind},
                )
            )
        elif command.category == "StartProof":
            reasons.append(
                command.reason(
                    "NESTED_PROOF_FORBIDDEN",
                    "目标 proof body 中不允许开始额外或嵌套证明。",
                    details={"names": list(command.names)},
                )
            )
        else:
            reasons.append(
                command.reason(
                    "PROOF_COMMAND_FORBIDDEN",
                    "目标 proof body 中只允许 VtProofStep。",
                    details={"category": command.category, "vernac_kind": command.kind},
                )
            )
    return reasons


def validate_proof_end(commands: Sequence[Command], target: ProofInterval) -> list[Reason]:
    command = commands[target.end]
    proof_end = command.record.get("proof_end")
    valid = (
        command.phase == "VernacSynPure"
        and command.kind == "VernacEndProof"
        and command.category == "Qed"
        and command.record.get("qed_action") == "KeepOpaque"
        and isinstance(proof_end, dict)
        and proof_end.get("kind") == "Opaque"
        and proof_end.get("name") is None
        and not has_controls(command)
        and not has_attributes(command)
    )
    if valid:
        return []
    return [
        command.reason(
            "INVALID_PROOF_END",
            "目标必须由唯一、无 control/attribute、无重命名的普通 opaque Qed. 结束。",
            details={
                "phase": command.phase,
                "vernac_kind": command.kind,
                "category": command.category,
                "qed_action": command.record.get("qed_action"),
                "proof_end": proof_end,
                "controls": command.record.get("controls"),
                "attributes": command.record.get("attributes"),
            },
        )
    ]


def validate_submission_proof_end(
    original: Sequence[Command],
    candidate: Sequence[Command],
    original_target: ProofInterval,
    candidate_target: ProofInterval,
) -> list[Reason]:
    """Keep an unfinished scaffold unchanged, or require a normal final Qed.

    A lemma worker normally edits one local proof_region while the enclosing
    theorem still ends in the baseline Admitted.  That unchanged terminator is
    allowed at submission time.  If the worker changes the enclosing proof
    terminator, however, the replacement must already satisfy the strict final
    policy instead of introducing a different proof-bypassing ending.
    """
    original_end = original[original_target.end]
    candidate_end = candidate[candidate_target.end]
    if original_end.comparison_key() == candidate_end.comparison_key():
        return []
    return validate_proof_end(candidate, candidate_target)


def require_key(from_prefix: str | None, module: str) -> str:
    return f"{from_prefix}::{module}" if from_prefix else module


def approved_require(command: Command, policy: Policy) -> tuple[bool, str]:
    if command.phase != "VernacSynterp" or command.kind != "VernacRequire":
        return False, "不是 VernacRequire"
    if command.category != "Sideff":
        return False, "VernacRequire 的分类不是 Sideff"
    if has_controls(command) or has_attributes(command):
        return False, "Require 带有 control 或 attribute"
    require = command.record.get("require")
    if not isinstance(require, dict):
        return False, "缺少 Require 元数据"
    mode = require.get("mode")
    if mode not in policy.allowed_require_modes:
        return False, f"Require mode {mode!r} 不在允许集合中"
    if require.get("has_categories") is not False:
        return False, "带 import categories 的 Require 不允许"
    from_prefix = require.get("from")
    if from_prefix is not None and not isinstance(from_prefix, str):
        return False, "Require 的 From 前缀格式无效"
    modules = require.get("modules")
    if not isinstance(modules, list) or not modules:
        return False, "Require 没有合法模块列表"
    keys: list[str] = []
    for module in modules:
        if not isinstance(module, dict) or not isinstance(module.get("name"), str):
            return False, "Require 模块元数据格式无效"
        if module.get("filter") != "All":
            return False, "带名称过滤器的 Require 不允许"
        keys.append(require_key(from_prefix, module["name"]))
    missing = [key for key in keys if key not in policy.allowed_requires]
    if missing:
        return False, f"模块不在精确白名单中：{', '.join(missing)}"
    return True, ""


def outside_target(
    commands: Sequence[Command], target: ProofInterval
) -> list[Command]:
    # Keep the theorem declaration.  Remove its proof body and closing command;
    # the candidate closing command is validated separately and may replace an
    # original Admitted/Defined placeholder.
    return [
        command
        for position, command in enumerate(commands)
        if not (target.start < position <= target.end)
    ]


def compare_exterior(
    original: Sequence[Command],
    candidate: Sequence[Command],
    original_target: ProofInterval,
    candidate_target: ProofInterval,
    policy: Policy,
) -> tuple[list[Reason], list[dict[str, Any]]]:
    original_exterior = outside_target(original, original_target)
    candidate_exterior = outside_target(candidate, candidate_target)
    reasons: list[Reason] = []
    allowed_additions: list[dict[str, Any]] = []
    original_position = 0
    candidate_position = 0

    while original_position < len(original_exterior) and candidate_position < len(candidate_exterior):
        original_command = original_exterior[original_position]
        candidate_command = candidate_exterior[candidate_position]
        if original_command.comparison_key() == candidate_command.comparison_key():
            original_position += 1
            candidate_position += 1
            continue
        approved, explanation = approved_require(candidate_command, policy)
        if approved:
            allowed_additions.append(
                {
                    "index": candidate_command.index,
                    "line": candidate_command.line,
                    "require": candidate_command.record.get("require"),
                }
            )
            candidate_position += 1
            continue
        reasons.append(
            candidate_command.reason(
                "EXTERIOR_AST_CHANGED",
                "proof 外的有序 AST 与原始文件不同，且候选节点不是批准的新增 Require。",
                details={
                    "original_index": original_command.index,
                    "original_kind": original_command.kind,
                    "candidate_kind": candidate_command.kind,
                    "require_rejection": explanation,
                },
            )
        )
        # Advance both sides to report subsequent independent differences.
        original_position += 1
        candidate_position += 1

    while candidate_position < len(candidate_exterior):
        candidate_command = candidate_exterior[candidate_position]
        approved, explanation = approved_require(candidate_command, policy)
        if approved:
            allowed_additions.append(
                {
                    "index": candidate_command.index,
                    "line": candidate_command.line,
                    "require": candidate_command.record.get("require"),
                }
            )
        else:
            reasons.append(
                candidate_command.reason(
                    "EXTERIOR_NODE_ADDED",
                    "proof 外新增了不允许的节点。",
                    details={
                        "vernac_kind": candidate_command.kind,
                        "category": candidate_command.category,
                        "require_rejection": explanation,
                    },
                )
            )
        candidate_position += 1

    while original_position < len(original_exterior):
        original_command = original_exterior[original_position]
        reasons.append(
            Reason(
                "EXTERIOR_NODE_REMOVED",
                "候选文件删除了 proof 外的原始节点。",
                file=original_command.file,
                index=original_command.index,
                line=original_command.line,
                details={"vernac_kind": original_command.kind},
            )
        )
        original_position += 1
    return reasons, allowed_additions


def validate(
    original_path: Path, candidate_path: Path, policy: Policy
) -> tuple[dict[str, Any], int]:
    original, original_reasons = load_commands(original_path)
    candidate, candidate_reasons = load_commands(candidate_path)
    reasons = original_reasons + candidate_reasons
    if reasons:
        return verdict(None, reasons, [], original, candidate), 1

    original_proofs, proof_reasons = build_proof_intervals(original, "原始文件")
    candidate_proofs, candidate_proof_reasons = build_proof_intervals(candidate, "候选文件")
    reasons.extend(proof_reasons)
    reasons.extend(candidate_proof_reasons)
    if reasons:
        return verdict(None, reasons, [], original, candidate), 1

    selection, selection_reasons = select_target(
        original,
        candidate,
        original_proofs,
        candidate_proofs,
        policy.target,
    )
    reasons.extend(selection_reasons)
    if selection is None:
        return verdict(None, reasons, [], original, candidate), 1

    original_target, candidate_target = selection
    target_name = list(original_target.names)
    reasons.extend(
        validate_target_start(
            original, candidate, original_target, candidate_target
        )
    )

    trusted_plugins = set(BUILTIN_TRUSTED_PLUGINS)
    trusted_plugins.update(policy.additional_trusted_plugins)
    if policy.trust_original_plugins:
        trusted_plugins.update(original_plugins(original))
    reasons.extend(
        validate_proof_body(candidate, candidate_target, policy, trusted_plugins)
    )
    if policy.stage == "final":
        reasons.extend(validate_proof_end(candidate, candidate_target))
    else:
        reasons.extend(
            validate_submission_proof_end(
                original,
                candidate,
                original_target,
                candidate_target,
            )
        )
    exterior_reasons, allowed_additions = compare_exterior(
        original,
        candidate,
        original_target,
        candidate_target,
        policy,
    )
    reasons.extend(exterior_reasons)
    result = verdict(target_name, reasons, allowed_additions, original, candidate)
    return result, 1 if reasons else 0


def verdict(
    target: list[str] | None,
    reasons: Sequence[Reason],
    allowed_additions: Sequence[dict[str, Any]],
    original: Sequence[Command],
    candidate: Sequence[Command],
) -> dict[str, Any]:
    rejected = bool(reasons)
    return {
        "accepted": not rejected,
        "rejected": rejected,
        "target": target,
        "reasons": [reason.as_json() for reason in reasons],
        "allowed_additions": list(allowed_additions),
        "summary": {
            "original_commands": len(original),
            "candidate_commands": len(candidate),
            "reason_count": len(reasons),
        },
        "semantic_checks_required": [
            "coqc",
            "target_kernel_type_equality",
            "Print Assumptions allowlist",
            "typing_flags",
            "dependency/coqchk policy",
        ],
    }


def parse_args(argv: Sequence[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="比较原始和候选的 Rocq classified astdump，并执行 proof 反作弊 AST 策略。"
    )
    parser.add_argument("original", type=Path, help="原始 .classified.jsonl")
    parser.add_argument("candidate", type=Path, help="候选 .classified.jsonl")
    parser.add_argument(
        "--stage",
        choices=("submission", "final"),
        default="final",
        help=(
            "submission 允许保留原始未完成 proof terminator；final 要求普通 opaque Qed.。"
        ),
    )
    parser.add_argument(
        "--target",
        help="目标 theorem 名称；省略时只在恰好一个 proof 发生变化时自动推断。",
    )
    parser.add_argument(
        "--allow-require",
        action="append",
        default=[],
        metavar="MODULE",
        help=(
            "允许新增的精确 Require 模块；From X Require Import Y 写成 X::Y。"
            "可重复指定，不支持前缀或通配符。"
        ),
    )
    parser.add_argument(
        "--allow-require-mode",
        action="append",
        choices=("Require", "Import", "Export"),
        default=None,
        help="允许的新增 Require 模式；默认只允许 Require Import（Import）。",
    )
    parser.add_argument(
        "--trusted-plugin",
        action="append",
        default=[],
        help="额外信任的 VernacExtend ext_plugin 精确名称；可重复指定。",
    )
    parser.add_argument(
        "--no-trust-original-plugins",
        action="store_true",
        help="不自动信任原始 AST 中已经出现的 extension plugins。",
    )
    parser.add_argument(
        "--allow-query",
        action="store_true",
        help="允许 proof body 中的 VtQuery；严格模式默认拒绝。",
    )
    parser.add_argument(
        "--allow-proof-attributes",
        action="store_true",
        help="允许 proof body 命令带 attributes；严格模式默认拒绝。",
    )
    parser.add_argument("--output", type=Path, help="将 verdict JSON 写入文件。")
    parser.add_argument("--compact", action="store_true", help="输出单行 JSON。")
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(sys.argv[1:] if argv is None else argv)
    policy = Policy(
        stage=args.stage,
        target=args.target,
        allowed_requires=frozenset(args.allow_require),
        allowed_require_modes=frozenset(args.allow_require_mode or ["Import"]),
        additional_trusted_plugins=frozenset(args.trusted_plugin),
        trust_original_plugins=not args.no_trust_original_plugins,
        allow_queries=args.allow_query,
        allow_attributes_in_proof=args.allow_proof_attributes,
    )
    result, exit_code = validate(args.original, args.candidate, policy)
    rendered = json.dumps(
        result,
        ensure_ascii=False,
        indent=None if args.compact else 2,
        sort_keys=False,
    )
    if args.output:
        args.output.write_text(rendered + "\n", encoding="utf-8")
    else:
        print(rendered)
    return exit_code


if __name__ == "__main__":
    raise SystemExit(main())
