#!/usr/bin/env python3

from __future__ import annotations

import json
import os
import subprocess
import sys
import tempfile
import textwrap
import unittest
from pathlib import Path

import run_casestudy_decompose as decompose


SOURCE = """Theorem demo : True.
Proof.
  exact I.
Qed.
"""

VALID_SKELETON = """Theorem demo : True.
Proof.
  (* proof_region begin owner: lemma admit_id: demo_leaf theorem: demo kind: semantic_bridge target: Hleaf plan_node: node1 depends_on: none source: context-derived input: none output: True layer: shape expected: exact normal_form: True evidence: coq:I *)
    assert (Hleaf : True).
  { admit. }
  (* proof_region end admit_id: demo_leaf *)
  exact Hleaf.
Admitted.
"""


class DecompositionRunnerTest(unittest.TestCase):
    def make_workspace(self, current: str = VALID_SKELETON) -> tuple[tempfile.TemporaryDirectory[str], Path, Path, Path]:
        temporary = tempfile.TemporaryDirectory()
        root = Path(temporary.name)
        source = root / "source.v"
        workspace = root / "workspace"
        theorem = workspace / "demo.v"
        workspace.mkdir()
        source.write_text(SOURCE, encoding="utf-8")
        theorem.write_text(current, encoding="utf-8")
        return temporary, source, workspace, theorem

    def write_ready_checkpoint(self, workspace: Path, theorem: Path) -> None:
        event = {
            "type": "tool_use",
            "timestamp": 1,
            "sessionID": "ses_test",
            "part": {
                "tool": "coqc",
                "state": {
                    "status": "completed",
                    "metadata": {
                        "decomposition_checkpoint": {
                            "status": "ready",
                            "terminal_ready": True,
                            "materialization_complete": True,
                            "source_hash": decompose.sha256_file(theorem),
                            "blockers": [],
                        }
                    },
                },
            },
        }
        (workspace.parent / "opencode_events.jsonl").write_text(json.dumps(event) + "\n", encoding="utf-8")

    def test_compile_checked_leaf_skeleton_is_success(self) -> None:
        temporary, source, workspace, theorem = self.make_workspace()
        with temporary:
            self.write_ready_checkpoint(workspace, theorem)
            success, info = decompose.check_decomposition_success(source, workspace, theorem)
            self.assertTrue(success, info)
            self.assertTrue(info["skeleton_compile_ok"])
            self.assertTrue(info["decomposition_verified"])
            self.assertEqual(info["admit_ids"], ["demo_leaf"])
            self.assertEqual(info["pending_leaf_count"], 1)
            self.assertEqual(info["coqc_exit_code"], 0)

    def test_compile_success_without_a_source_bound_checkpoint_is_not_decomposition_success(self) -> None:
        temporary, source, workspace, theorem = self.make_workspace()
        with temporary:
            success, info = decompose.check_decomposition_success(source, workspace, theorem)
            self.assertFalse(success)
            self.assertTrue(info["skeleton_compile_ok"])
            self.assertTrue(
                any("no source-bound decomposition checkpoint" in issue for issue in info["decomposition_issues"])
            )

    def test_extracts_a_structured_terminal_plan_verdict(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            trace = Path(temporary) / "events.jsonl"
            verdict = {
                "status": "semantic_incomplete",
                "source_hash": "abc",
                "theorem_source_hash": "def",
                "semantic_fingerprint": "plan",
                "blockers": ["missing premise"],
                "recoverable": True,
                "planning_generation": 0,
                "failure_fingerprint": "failure",
                "best_semantic_fingerprint": "best-plan",
                "evaluated_at": 1,
            }
            event = {
                "type": "tool_use",
                "part": {
                    "tool": "proof_plan",
                    "state": {
                        "status": "completed",
                        "metadata": {
                            "planning_status": "exhausted",
                            "recommended_action": "start_new_plan_generation",
                            "terminal_verdict": verdict,
                        },
                    },
                },
            }
            trace.write_text(json.dumps(event) + "\n", encoding="utf-8")
            self.assertEqual(decompose.base.extract_attempt_decomposition_terminal(trace, 0), verdict)

    def test_extracts_materialization_livelock_receipt(self) -> None:
        receipt = {
            "status": "materialization_livelock",
            "recoverable": True,
            "reason": "plan_node_identifier_mismatch_or_stagnation",
            "missing_plan_nodes": ["if_feasible"],
        }
        terminal_text = (
            "materialization_livelock: "
            + json.dumps(receipt)
            + "\nThe staged transaction is preserved."
        )
        self.assertEqual(
            decompose.base.extract_materialization_livelock(terminal_text),
            receipt,
        )

    def test_runner_tracks_staged_transaction_and_compiler_certificate(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            theorem = root / "demo.v"
            theorem.write_text(VALID_SKELETON, encoding="utf-8")
            trace = root / "events.jsonl"
            staged_hash = "a" * 64
            transaction = {
                "file": str(theorem),
                "source_hash": staged_hash,
                "revision": 3,
                "certified_revision": 3,
                "certified_region_count": 1,
                "certified_unresolved_debt": 2,
                "validation_pending": False,
                "staged": True,
            }
            events = [
                {
                    "type": "tool_use",
                    "part": {
                        "tool": "edit",
                        "state": {
                            "status": "completed",
                            "metadata": {"proof_edit_transaction": transaction},
                        },
                    },
                },
                {
                    "type": "tool_use",
                    "part": {
                        "tool": "checkpoint",
                        "state": {
                            "status": "completed",
                            "metadata": {
                                "proof_edit_transaction": transaction,
                                "proof_status": {
                                    "proof_progress": {
                                        "accepted": True,
                                        "level": "hard",
                                        "receipt": {
                                            "kind": "region_certified",
                                            "admit_id": "demo_leaf",
                                        },
                                    }
                                },
                                "proof_region_lifecycle": {
                                    "action": "certified",
                                    "admit_id": "demo_leaf",
                                    "compiler_signature": "compiler-1",
                                },
                            },
                        },
                    },
                },
            ]
            trace.write_text(
                "".join(json.dumps(event) + "\n" for event in events),
                encoding="utf-8",
            )

            runtime = decompose.base.extract_proof_runtime_state(trace, 0, theorem)
            self.assertEqual(runtime["transaction"]["source_hash"], staged_hash)
            self.assertEqual(runtime["transaction"]["certified_region_count"], 1)
            self.assertIsNotNone(runtime["certificate_signature"])

            disk_hash = decompose.sha256_file(theorem)
            self.assertIn(
                staged_hash,
                decompose.base.proof_runtime_source_hashes(disk_hash, runtime),
            )
            self.assertNotEqual(
                decompose.base.proof_runtime_fingerprint(disk_hash, runtime),
                decompose.base.proof_runtime_fingerprint(
                    disk_hash,
                    {"transaction": None, "certificate_signature": None},
                ),
            )

    def test_runtime_fingerprint_changes_when_only_staged_source_changes(self) -> None:
        disk_hash = "d" * 64
        first = {
            "transaction": {"source_hash": "1" * 64},
            "certificate_signature": None,
        }
        second = {
            "transaction": {"source_hash": "2" * 64},
            "certificate_signature": None,
        }
        self.assertNotEqual(
            decompose.base.proof_runtime_fingerprint(disk_hash, first),
            decompose.base.proof_runtime_fingerprint(disk_hash, second),
        )

    def test_same_session_recovery_retries_once_before_fresh_session(self) -> None:
        tracked, streak, use_fresh = decompose.base._same_session_retry_or_fresh(
            "ses_one", None, 0
        )
        self.assertEqual((tracked, streak, use_fresh), ("ses_one", 1, False))

        tracked, streak, use_fresh = decompose.base._same_session_retry_or_fresh(
            "ses_one", tracked, streak
        )
        self.assertEqual((tracked, streak, use_fresh), ("ses_one", 2, True))

        tracked, streak, use_fresh = decompose.base._same_session_retry_or_fresh(
            "ses_two", tracked, streak
        )
        self.assertEqual((tracked, streak, use_fresh), ("ses_two", 1, False))

    def test_plan_generation_recovery_handoff_is_compact_and_actionable(self) -> None:
        prompt = decompose.base.build_continuation_prompt(
            Path("demo.v"),
            "demo",
            "Theorem demo : True.",
            proof_info={
                "decomposition_plan_generation_recovery": {
                    "planning_generation": 0,
                    "blockers": ["parent_equivalent_leaf: root cannot be delegated"],
                }
            },
            retry_index=2,
            max_retries=20,
            segmented_proof_workflow=True,
        )
        self.assertIn("authorized one more planning generation", prompt)
        self.assertIn("parent_equivalent_leaf", prompt)
        self.assertIn("do not materialize a rejected plan", prompt)

    def test_terminal_plan_recovery_strategy_uses_fresh_session_under_budget(self) -> None:
        self.assertEqual(
            decompose.base.decomposition_terminal_recovery_strategy(
                {"recoverable": True}, 3, 20
            ),
            "retry_same_session",
        )
        self.assertEqual(
            decompose.base.decomposition_terminal_recovery_strategy(
                {"recoverable": False}, 3, 20
            ),
            "fresh_session",
        )

    def test_terminal_plan_recovery_strategy_honors_retry_limit(self) -> None:
        for recoverable in (True, False):
            with self.subTest(recoverable=recoverable):
                self.assertEqual(
                    decompose.base.decomposition_terminal_recovery_strategy(
                        {"recoverable": recoverable}, 21, 20
                    ),
                    "retry_limit",
                )

    def test_terminal_plan_fresh_attempt_handoff_preserves_workspace_and_blockers(self) -> None:
        prompt = decompose.base.build_continuation_prompt(
            Path("demo.v"),
            "demo",
            "Theorem demo : True.",
            proof_info={
                "decomposition_terminal_fresh_attempt": {
                    "planning_generation": 1,
                    "semantic_fingerprint": "rejected-plan-123",
                    "blockers": ["composition_target_mismatch: missing dependency"],
                }
            },
            retry_index=3,
            max_retries=20,
            segmented_proof_workflow=True,
        )
        self.assertIn("starts a fresh proof attempt", prompt)
        self.assertIn("not completion of the experiment", prompt)
        self.assertIn("does not reset the workspace", prompt)
        self.assertIn("compiler-certified regions", prompt)
        self.assertIn("composition_target_mismatch", prompt)
        self.assertIn("rejected-plan-123", prompt)
        self.assertNotIn("entire experiment is complete", prompt)

    def test_missing_skeleton_handoff_does_not_claim_same_session_is_fresh(self) -> None:
        prompt = decompose.base.build_continuation_prompt(
            Path("demo.v"),
            "demo",
            "Theorem demo : True.",
            proof_info={"missing_segmented_skeleton": True},
            retry_index=2,
            max_retries=20,
            segmented_proof_workflow=True,
        )
        self.assertIn("runner may preserve the current model session once", prompt)
        self.assertNotIn("This is a fresh recovery session", prompt)

    def test_segmented_workflow_enables_terminal_receipts_without_env_flag(self) -> None:
        self.assertTrue(
            decompose.base.decomposition_terminal_receipts_enabled(
                segmented_proof_workflow=True,
                env={},
            )
        )
        self.assertTrue(
            decompose.base.decomposition_terminal_receipts_enabled(
                segmented_proof_workflow=False,
                env={"OPENCODE_PROOF_WORKFLOW_MODE": "decomposition"},
            )
        )
        self.assertFalse(
            decompose.base.decomposition_terminal_receipts_enabled(
                segmented_proof_workflow=False,
                env={},
            )
        )

    def test_admit_outside_leaf_region_is_rejected(self) -> None:
        invalid = """Theorem demo : True.
Proof.
  admit.
Admitted.
"""
        temporary, source, workspace, theorem = self.make_workspace(invalid)
        with temporary:
            success, info = decompose.check_decomposition_success(source, workspace, theorem)
            self.assertFalse(success)
            self.assertTrue(info["skeleton_compile_ok"])
            self.assertTrue(any("outside lemma-owned proof_regions" in issue for issue in info["decomposition_issues"]))

    def test_finalizer_writes_snapshot_manifest_and_trace_summary(self) -> None:
        temporary, source, workspace, theorem = self.make_workspace()
        with temporary:
            run_dir = workspace.parent / "case"
            run_workspace = run_dir / "workspace"
            run_workspace.mkdir(parents=True)
            run_theorem = run_workspace / theorem.name
            run_theorem.write_text(theorem.read_text(encoding="utf-8"), encoding="utf-8")
            event = {
                "type": "step_finish",
                "timestamp": 1,
                "sessionID": "ses_test",
                "part": {"tokens": {"total": 7}},
            }
            self.write_ready_checkpoint(run_workspace, run_theorem)
            with (run_dir / "opencode_events.jsonl").open("a", encoding="utf-8") as handle:
                handle.write(json.dumps(event) + "\n")
            progress = run_dir.parent / "progress.jsonl"
            summary = {
                "workspace": "case",
                "source_theorem_file": str(source),
                "runtime_workspace_dir": str(run_workspace),
                "theorem_file": run_theorem.name,
                "theorem_name": "demo",
                "status": "success",
            }

            finalized = decompose.finalize_decomposition_artifacts(summary, run_dir=run_dir, progress_file=progress)

            self.assertEqual(finalized["status"], "success")
            self.assertTrue(finalized["decomposition_verified"])
            self.assertTrue((run_dir / "final.v").is_file())
            self.assertTrue((run_dir / "decomposition_manifest.json").is_file())
            self.assertTrue((run_dir / "trace_summary.json").is_file())
            self.assertTrue((run_dir / "compile.log").is_file())
            trace_summary = json.loads((run_dir / "trace_summary.json").read_text(encoding="utf-8"))
            self.assertEqual(trace_summary["event_trace"]["total_tokens"], 7)
            self.assertEqual(trace_summary["event_trace"]["sessions"], ["ses_test"])

    def test_cli_end_to_end_with_fake_opencode(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            cases = root / "cases"
            case = cases / "case-a"
            case.mkdir(parents=True)
            (case / "demo.v").write_text(SOURCE, encoding="utf-8")
            (case / "proof.tex").write_text("A one-step proof.", encoding="utf-8")
            prosa = root / "prosa"
            prosa.mkdir()
            results = root / "results"
            fake = root / "fake-opencode.py"
            fake.write_text(
                textwrap.dedent(
                    """\
                    #!/usr/bin/env python3
                    import json
                    import hashlib
                    import os
                    import sys
                    from pathlib import Path

                    args = sys.argv[1:]
                    workspace = Path(args[args.index("--dir") + 1])
                    target_name = args[args.index("--file") + 1] if "--file" in args else "demo.v"
                    target = workspace / target_name
                    target.write_text('''Theorem demo : True.
                    Proof.
                      (* proof_region begin owner: lemma admit_id: demo_leaf theorem: demo kind: semantic_bridge target: Hleaf plan_node: node1 depends_on: none source: context-derived input: none output: True layer: shape expected: exact normal_form: True evidence: coq:I *)
                      assert (Hleaf : True).
                      { admit. }
                      (* proof_region end admit_id: demo_leaf *)
                      exact Hleaf.
                    Admitted.
                    ''', encoding="utf-8")

                    session = "ses_e2e"
                    trace_root = Path(os.environ["OPENCODE_TRACE_DIR"])
                    trace_run = trace_root / f"run-e2e-{os.getpid()}"
                    (trace_run / session).mkdir(parents=True)
                    (trace_run / "run.json").write_text(json.dumps({"id": "e2e", "pid": os.getpid(), "argv": args, "cwd": str(workspace)}), encoding="utf-8")
                    (trace_run / "requests.jsonl").write_text(json.dumps({"type": "request", "session_id": session}) + "\\n", encoding="utf-8")
                    (trace_run / session / "summary.json").write_text(json.dumps({"sessionID": session, "steps": 1, "events": 3}), encoding="utf-8")
                    (trace_run / "summary.json").write_text(json.dumps({"id": "e2e", "sessions": [session]}), encoding="utf-8")

                    events = [
                        {"type": "step_start", "timestamp": 1, "sessionID": session, "part": {}},
                        {"type": "tool_use", "timestamp": 2, "sessionID": session, "part": {"tool": "edit"}},
                        {"type": "tool_use", "timestamp": 2, "sessionID": session, "part": {"tool": "coqc", "state": {"status": "completed", "metadata": {"decomposition_checkpoint": {"status": "ready", "terminal_ready": True, "materialization_complete": True, "source_hash": hashlib.sha256(target.read_bytes()).hexdigest(), "blockers": []}}}}},
                        {"type": "step_finish", "timestamp": 3, "sessionID": session, "part": {"tokens": {"total": 11}}},
                    ]
                    for event in events:
                        print(json.dumps(event), flush=True)
                    """
                ),
                encoding="utf-8",
            )
            fake.chmod(0o755)

            env = os.environ.copy()
            env.update(
                {
                    "OPENCODE_RUN_NOHUP": "0",
                    "OPENCODE_RESULTS_ROOT": str(results),
                    "OPENCODE_RESULT_PREFIX": "decompose-e2e",
                    "OPENCODE_MIN_PROSA_SOURCE_DIR": str(prosa),
                    "OPENCODE_FULL_PROSA_SOURCE_DIR": str(prosa),
                }
            )
            command = [
                sys.executable,
                str(Path(decompose.__file__)),
                "--cases-dir",
                str(cases),
                "--opencode-bin",
                str(fake),
                "--stage-full-casestudy-workspace",
                "--full-prosa",
                "--full-prosa-source-dir",
                str(prosa),
                "--trace-requests",
                "case-a",
            ]
            completed = subprocess.run(command, env=env, capture_output=True, text=True, timeout=30)
            self.assertEqual(completed.returncode, 0, completed.stdout + completed.stderr)

            run_roots = list(results.glob("decompose-e2e_*"))
            self.assertEqual(len(run_roots), 1)
            run_root = run_roots[0]
            case_result = run_root / "case-a"
            for name in (
                "final.v",
                "opencode_events.jsonl",
                "trace_summary.json",
                "decomposition_manifest.json",
                "compile.log",
                "result.json",
            ):
                self.assertTrue((case_result / name).is_file(), name)
            self.assertTrue(list((case_result / "request_traces").rglob("requests.jsonl")))
            result = json.loads((case_result / "result.json").read_text(encoding="utf-8"))
            self.assertEqual(result["status"], "success")
            self.assertTrue(result["decomposition_verified"])
            self.assertTrue(result["skeleton_compile_ok"])
            self.assertEqual(result["completion_mode"], "decomposition")
            config = json.loads((run_root / "config.json").read_text(encoding="utf-8"))
            self.assertEqual(config["completion_mode"], "decomposition")


if __name__ == "__main__":
    unittest.main()
