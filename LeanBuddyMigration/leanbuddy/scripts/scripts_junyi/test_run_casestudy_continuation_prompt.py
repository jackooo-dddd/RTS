#!/usr/bin/env python3

from __future__ import annotations

import json
import tempfile
import unittest
from pathlib import Path

import run_casestudy_our_minprosa as runner


class ContinuationPromptTest(unittest.TestCase):
    def assert_fresh_session_anchor(self, prompt: str) -> None:
        self.assertIn("if `proof.tex` has not yet been read in that live session", prompt)
        self.assertIn("MUST first use the read tool on `proof.tex`", prompt)
        self.assertIn("before calling `task` or attempting any lemma dispatch", prompt)
        self.assertIn("do not reread it repeatedly", prompt)

    def test_our_runner_requires_paper_anchor_before_fresh_dispatch(self) -> None:
        prompt = runner.build_continuation_prompt(
            Path("Lemma4.v"),
            "Lemma4_05",
            "Lemma Lemma4_05 : True.",
            proof_info={"admit_skeleton_retained": True},
            retry_index=3,
            max_retries=20,
            segmented_proof_workflow=True,
        )
        self.assert_fresh_session_anchor(prompt)

    def test_base_runner_requires_paper_anchor_before_fresh_dispatch(self) -> None:
        prompt = runner.base.build_continuation_prompt(
            Path("Lemma4.v"),
            "Lemma4_05",
            "Lemma Lemma4_05 : True.",
            proof_info={"admit_skeleton_retained": True},
            retry_index=3,
            max_retries=20,
            segmented_proof_workflow=True,
        )
        self.assert_fresh_session_anchor(prompt)

    def test_segmented_runner_always_enables_structured_controller_mode(self) -> None:
        self.assertEqual(
            runner._proof_workflow_env(True, None),
            {"OPENCODE_PROOF_WORKFLOW_MODE": "prooftex_structured_workflow"},
        )
        self.assertEqual(
            runner._proof_workflow_env(True, {"EXTRA": "1"}),
            {
                "EXTRA": "1",
                "OPENCODE_PROOF_WORKFLOW_MODE": "prooftex_structured_workflow",
            },
        )

    def test_runner_preserves_explicit_controller_mode_override(self) -> None:
        self.assertEqual(
            runner._proof_workflow_env(
                True,
                {"OPENCODE_PROOF_WORKFLOW_MODE": runner.DIRECT_PROSA_PROBE_MODE},
            ),
            {"OPENCODE_PROOF_WORKFLOW_MODE": runner.DIRECT_PROSA_PROBE_MODE},
        )
        self.assertIsNone(runner._proof_workflow_env(False, None))

    def test_detects_reasoning_only_length_exhaustion(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            trace = Path(temporary) / "requests.jsonl"
            trace.write_text(
                json.dumps(
                    {
                        "type": "request",
                        "finish": {"reason": "length"},
                        "usage": {
                            "output_tokens": 32_000,
                            "reasoning_tokens": 32_000,
                        },
                    }
                )
                + "\n",
                encoding="utf-8",
            )
            outcome = runner.base.extract_attempt_request_outcome(trace, 0)
        self.assertTrue(outcome["reasoning_output_exhausted"])
        self.assertEqual(outcome["finish_reasons"], ["length"])
        self.assertEqual(outcome["reasoning_fraction"], 1.0)

    def test_visible_tool_response_is_not_reasoning_exhaustion(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            trace = Path(temporary) / "requests.jsonl"
            trace.write_text(
                json.dumps(
                    {
                        "type": "request",
                        "finish": {"reason": "tool-calls"},
                        "usage": {
                            "output_tokens": 4_000,
                            "reasoning_tokens": 3_900,
                        },
                    }
                )
                + "\n",
                encoding="utf-8",
            )
            outcome = runner.base.extract_attempt_request_outcome(trace, 0)
        self.assertFalse(outcome["reasoning_output_exhausted"])

    def test_noop_recovery_charges_retry_on_fifth_consecutive_noop(self) -> None:
        self.assertFalse(runner.base._should_charge_noop_recovery(4))
        self.assertTrue(runner.base._should_charge_noop_recovery(5))

    def test_reasoning_exhaustion_handoff_requires_an_immediate_tool_action(self) -> None:
        prompt = runner.base.build_continuation_prompt(
            Path("Method1_10.v"),
            "Method1_10_09",
            "Lemma Method1_10_09 : True.",
            proof_info={
                "reasoning_output_exhausted_recovery": {
                    "consecutive_exhaustions": 2,
                }
            },
            retry_index=4,
            max_retries=20,
        )
        self.assertIn("exhausted its output allowance in hidden reasoning", prompt)
        self.assertIn("first externally visible action a tool call", prompt)

    def test_compile_error_trimming_preserves_the_actionable_tail(self) -> None:
        warnings = "\n".join(
            f'File "./Method1_10.v", line 1, characters 0-38:\nWarning: noisy warning {index}'
            for index in range(120)
        )
        error = (
            'File "./Method1_10.v", line 360, characters 49-61:\n'
            "Error: Cannot apply lemma IN_CI"
        )
        trimmed = runner.base._trim_compile_error(f"{warnings}\n{error}")
        self.assertLessEqual(len(trimmed), 4000)
        self.assertIn("line 360", trimmed)
        self.assertIn("Cannot apply lemma IN_CI", trimmed)
        self.assertIn("earlier Rocq warnings omitted", trimmed)

    def test_continuation_prompt_receives_real_error_after_long_warnings(self) -> None:
        warnings = "warning-prefix\n" * 1000
        error = 'File "./Method1_10.v", line 360:\nError: Cannot apply lemma IN_CI'
        prompt = runner.build_continuation_prompt(
            Path("Method1_10.v"),
            "Method1_10_09",
            "Lemma Method1_10_09 : True.",
            proof_info={"compile_error": warnings + error},
            retry_index=9,
            max_retries=20,
        )
        self.assertIn("Cannot apply lemma IN_CI", prompt)
        self.assertIn("line 360", prompt)


if __name__ == "__main__":
    unittest.main()
