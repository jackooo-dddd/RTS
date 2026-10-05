#!/usr/bin/env python3
"""Generate end-to-end Rocq AST-validator examples from a Lemma4 template."""

from __future__ import annotations

import argparse
import json
from dataclasses import dataclass
from pathlib import Path
from typing import Callable


STDLIB_IMPORT = "From Stdlib Require Import Lists.List.\n\n"
MATHCOMP_IMPORT = (
    "From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq "
    "fintype bigop div path."
)
PROOF_MARKER = "\nProof.\n"
PROOF_END = "\nQed.\nEnd Lemma4."
TARGET_STATEMENT = (
    "      Lemma Lemma4_09 :\n"
    "         response_time_bounded_by tsk "
    "(chi - (job_arrival j - t0 sched j))."
)


@dataclass(frozen=True)
class Example:
    filename: str
    expected: str
    description: str
    transform: Callable[[str], str]
    allowed_requires: tuple[str, ...] = ()
    expected_reason: str | None = None


def replace_once(text: str, old: str, new: str) -> str:
    count = text.count(old)
    if count != 1:
        raise ValueError(f"expected one occurrence of {old!r}, found {count}")
    return text.replace(old, new, 1)


def after_proof(command: str) -> Callable[[str], str]:
    return lambda text: replace_once(text, PROOF_MARKER, PROOF_MARKER + command)


def replace_qed(ending: str) -> Callable[[str], str]:
    return lambda text: replace_once(
        text, PROOF_END, f"\n{ending}.\nEnd Lemma4."
    )


def add_import(command: str) -> Callable[[str], str]:
    return lambda text: replace_once(
        text, MATHCOMP_IMPORT, MATHCOMP_IMPORT + "\n" + command
    )


def examples(template: str) -> list[Example]:
    if STDLIB_IMPORT in template:
        raise ValueError(
            "the baseline template still contains the unapproved Stdlib import"
        )
    clean = lambda _text: template

    def from_clean(transform: Callable[[str], str]) -> Callable[[str], str]:
        return lambda _text: transform(clean(_text))

    return [
        Example(
            "case01_pass_baseline.v",
            "accept",
            "原模板证明，移除原始文件中不存在的 Stdlib import",
            clean,
        ),
        Example(
            "case02_pass_comments_whitespace.v",
            "accept",
            "只在 proof 外增加注释和空白",
            from_clean(
                lambda text: replace_once(
                    text,
                    MATHCOMP_IMPORT,
                    MATHCOMP_IMPORT
                    + "\n\n(* AST test: comments and whitespace are ignored. *)\n\n",
                )
            ),
        ),
        Example(
            "case03_pass_idtac.v",
            "accept",
            "proof 内增加普通 Ltac proof step",
            from_clean(after_proof("  idtac.\n")),
        ),
        Example(
            "case04_pass_local_have.v",
            "accept",
            "proof 内增加带子证明的局部 have",
            from_clean(
                after_proof(
                    "  have AST_TEST_LOCAL_TRUE : True.\n"
                    "  {\n"
                    "    exact I.\n"
                    "  }\n"
                )
            ),
        ),
        Example(
            "case05_pass_allowed_prosa_import.v",
            "accept",
            "proof 外增加精确白名单中的 Prosa Require Import",
            from_clean(
                add_import(
                    "Require Import "
                    "prosa.classic.model.schedule.apa.response_time."
                )
            ),
            allowed_requires=(
                "prosa.classic.model.schedule.apa.response_time",
            ),
        ),
        Example(
            "case06_pass_allowed_mathcomp_import.v",
            "accept",
            "proof 外增加精确白名单中的 MathComp Require Import",
            from_clean(
                add_import("From mathcomp Require Import ssreflect.")
            ),
            allowed_requires=("mathcomp::ssreflect",),
        ),
        Example(
            "case07_reject_unapproved_stdlib_import.v",
            "reject",
            "原模板额外包含未列入白名单的 Stdlib import",
            lambda text: STDLIB_IMPORT + text,
            expected_reason="EXTERIOR_AST_CHANGED",
        ),
        Example(
            "case08_reject_outside_hypothesis.v",
            "reject",
            "proof 外新增 Hypothesis",
            from_clean(
                lambda text: replace_once(
                    text,
                    "      Lemma Lemma4_09 :",
                    "      Hypothesis AST_TEST_H_TRUE : True.\n\n"
                    "      Lemma Lemma4_09 :",
                )
            ),
            expected_reason="EXTERIOR_AST_CHANGED",
        ),
        Example(
            "case09_reject_outside_definition_change.v",
            "reject",
            "修改 proof 外 Definition W 的定义体",
            from_clean(
                lambda text: replace_once(text, "minn (e_k-1)", "minn e_k")
            ),
            expected_reason="EXTERIOR_AST_CHANGED",
        ),
        Example(
            "case10_reject_target_statement_change.v",
            "reject",
            "修改目标 theorem 声明，并同步调整 proof 使其仍可证明",
            from_clean(
                lambda text: after_proof("  move=> _.\n")(
                    replace_once(
                        text,
                        TARGET_STATEMENT,
                        "      Lemma Lemma4_09 :\n"
                        "         True -> response_time_bounded_by tsk "
                        "(chi - (job_arrival j - t0 sched j)).",
                    )
                )
            ),
            expected_reason="TARGET_DECLARATION_CHANGED",
        ),
        Example(
            "case11_reject_axiom_inside_proof.v",
            "reject",
            "proof 内新增 Axiom",
            from_clean(after_proof("  Axiom AST_TEST_AXIOM : False.\n")),
            expected_reason="PROOF_SIDE_EFFECT",
        ),
        Example(
            "case12_reject_definition_inside_proof.v",
            "reject",
            "proof 内新增 Definition",
            from_clean(
                after_proof("  Definition AST_TEST_DEFINITION : True := I.\n")
            ),
            expected_reason="PROOF_SIDE_EFFECT",
        ),
        Example(
            "case13_reject_unset_guard_checking.v",
            "reject",
            "proof 内关闭 Guard Checking",
            from_clean(after_proof("  Unset Guard Checking.\n")),
            expected_reason="PROOF_SYNTERP_FORBIDDEN",
        ),
        Example(
            "case14_reject_set_universe_polymorphism.v",
            "reject",
            "proof 内修改 Universe Polymorphism 选项",
            from_clean(after_proof("  Set Universe Polymorphism.\n")),
            expected_reason="PROOF_SYNTERP_FORBIDDEN",
        ),
        Example(
            "case15_reject_require_inside_proof.v",
            "reject",
            "proof 内执行即使已列入白名单的 Prosa Require Import",
            from_clean(
                after_proof(
                    "  Require Import "
                    "prosa.classic.model.schedule.apa.response_time.\n"
                )
            ),
            allowed_requires=(
                "prosa.classic.model.schedule.apa.response_time",
            ),
            expected_reason="PROOF_SYNTERP_FORBIDDEN",
        ),
        Example(
            "case16_reject_query_inside_proof.v",
            "reject",
            "proof 内保留 Check 查询",
            from_clean(after_proof("  Check True.\n")),
            expected_reason="PROOF_QUERY_FORBIDDEN",
        ),
        Example(
            "case17_reject_fail_control.v",
            "reject",
            "proof step 使用 Fail control wrapper",
            from_clean(
                after_proof("  Fail fail \"expected AST test failure\".\n")
            ),
            expected_reason="PROOF_CONTROL_FORBIDDEN",
        ),
        Example(
            "case18_reject_admitted.v",
            "reject",
            "以 Admitted 放弃证明",
            from_clean(replace_qed("Admitted")),
            expected_reason="INVALID_PROOF_END",
        ),
        Example(
            "case19_reject_defined.v",
            "reject",
            "以透明 Defined 结束而不是 opaque Qed",
            from_clean(replace_qed("Defined")),
            expected_reason="INVALID_PROOF_END",
        ),
        Example(
            "case20_reject_abort.v",
            "reject",
            "以 Abort 丢弃证明",
            from_clean(replace_qed("Abort")),
            expected_reason="INVALID_PROOF_END",
        ),
    ]


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("template", type=Path)
    parser.add_argument("output_dir", type=Path)
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    template = args.template.read_text(encoding="utf-8")
    cases = examples(template)
    if len(cases) != 20:
        raise AssertionError(f"expected 20 cases, got {len(cases)}")
    args.output_dir.mkdir(parents=True, exist_ok=True)
    manifest: list[dict[str, object]] = []
    for case in cases:
        source = case.transform(template)
        destination = args.output_dir / case.filename
        destination.write_text(source, encoding="utf-8")
        manifest.append(
            {
                "filename": case.filename,
                "expected": case.expected,
                "description": case.description,
                "allowed_requires": list(case.allowed_requires),
                "expected_reason": case.expected_reason,
            }
        )
    (args.output_dir / "manifest.json").write_text(
        json.dumps(manifest, ensure_ascii=False, indent=2) + "\n",
        encoding="utf-8",
    )
    print(f"generated {len(cases)} cases in {args.output_dir}")


if __name__ == "__main__":
    main()
