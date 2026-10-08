#!/usr/bin/env python3

from __future__ import annotations

import json
import sys
import tempfile
import unittest
from pathlib import Path
from typing import Any

sys.path.insert(0, str(Path(__file__).resolve().parent))

from validate_classified_ast import Policy, normalize_ast, validate  # noqa: E402


PLUGIN = "rocq-runtime.plugins.ltac"


def ast(tag: str, payload: Any = None, line: int = 1) -> dict[str, Any]:
    return {
        "loc": {"line_nb": line, "line_nb_last": line, "bp": line, "ep": line + 1},
        "v": {"tag": tag, "payload": payload},
    }


def record(
    index: int,
    phase: str,
    kind: str,
    category: str,
    *,
    names: list[str] | None = None,
    payload: Any = None,
    qed_action: str | None = None,
    proof_end: dict[str, Any] | None = None,
    controls: list[str] | None = None,
    attributes: list[str] | None = None,
    require: dict[str, Any] | None = None,
    extension: dict[str, Any] | None = None,
) -> dict[str, Any]:
    return {
        "schema_version": 1,
        "index": index,
        "phase": phase,
        "vernac_kind": kind,
        "source_line": index,
        "source_end_line": index,
        "byte_start": index,
        "byte_end": index + 1,
        "controls": [] if controls is None else controls,
        "attributes": [] if attributes is None else attributes,
        "require": require,
        "extension": extension,
        "proof_end": proof_end,
        "classification": category,
        "category": category,
        "names": [] if names is None else names,
        "when": "Later" if category == "Sideff" else None,
        "opacity_guarantee": "GuaranteesOpacity" if category == "StartProof" else None,
        "qed_action": qed_action,
        "proof_block_detection": None,
        "ast": ast(kind, payload, index),
    }


def start(index: int, name: str = "target", statement: str = "P") -> dict[str, Any]:
    return record(
        index,
        "VernacSynPure",
        "VernacStartTheoremProof",
        "StartProof",
        names=[name],
        payload={"name": name, "statement": statement},
    )


def tactic(index: int, text: str, plugin: str = PLUGIN) -> dict[str, Any]:
    return record(
        index,
        "VernacSynterp",
        "VernacExtend",
        "ProofStep",
        payload=text,
        extension={"plugin": plugin, "entry": "VernacSolve", "index": 0},
    )


def qed(index: int, action: str = "KeepOpaque") -> dict[str, Any]:
    if action == "KeepOpaque":
        end = {"kind": "Opaque", "name": None}
    elif action == "KeepAxiom":
        end = {"kind": "Admitted", "name": None}
    elif action == "KeepDefined":
        end = {"kind": "Transparent", "name": None}
    else:
        end = {"kind": "Abort", "name": None}
    return record(
        index,
        "VernacSynPure",
        "VernacEndProof" if action != "Drop" else "VernacAbort",
        "Qed",
        payload=action,
        qed_action=action,
        proof_end=end,
    )


def side_effect(index: int, kind: str) -> dict[str, Any]:
    phase = "VernacSynterp" if kind == "VernacSetOption" else "VernacSynPure"
    return record(index, phase, kind, "Sideff", payload=kind)


def require_import(index: int, module: str, from_prefix: str | None = None) -> dict[str, Any]:
    require = {
        "from": from_prefix,
        "mode": "Import",
        "has_categories": False,
        "modules": [{"name": module, "filter": "All"}],
    }
    return record(
        index,
        "VernacSynterp",
        "VernacRequire",
        "Sideff",
        payload=require,
        require=require,
    )


def default_policy(**changes: Any) -> Policy:
    values = {
        "stage": "final",
        "target": None,
        "allowed_requires": frozenset(),
        "allowed_require_modes": frozenset({"Import"}),
        "additional_trusted_plugins": frozenset(),
        "trust_original_plugins": True,
        "allow_queries": False,
        "allow_attributes_in_proof": False,
    }
    values.update(changes)
    return Policy(**values)


class ValidatorTests(unittest.TestCase):
    def run_validator(
        self,
        original: list[dict[str, Any]],
        candidate: list[dict[str, Any]],
        policy: Policy | None = None,
    ) -> tuple[dict[str, Any], int]:
        with tempfile.TemporaryDirectory() as directory:
            original_path = Path(directory) / "original.jsonl"
            candidate_path = Path(directory) / "candidate.jsonl"
            original_path.write_text(
                "".join(json.dumps(item) + "\n" for item in original), encoding="utf-8"
            )
            candidate_path.write_text(
                "".join(json.dumps(item) + "\n" for item in candidate), encoding="utf-8"
            )
            return validate(original_path, candidate_path, policy or default_policy())

    @staticmethod
    def codes(result: dict[str, Any]) -> set[str]:
        return {reason["code"] for reason in result["reasons"]}

    def test_normalization_removes_object_and_serlib_list_locations(self) -> None:
        left = {
            "loc": {"line_nb": 1},
            "v": [["v", "same"], ["loc", [["line_nb", "1"]]]],
        }
        right = {
            "loc": {"line_nb": 99},
            "v": [["v", "same"], ["loc", [["line_nb", "99"]]]],
        }
        self.assertEqual(normalize_ast(left), normalize_ast(right))

    def test_accepts_changed_proof_steps_and_opaque_qed(self) -> None:
        result, exit_code = self.run_validator(
            [start(1), tactic(2, "old"), qed(3)],
            [start(1), tactic(2, "new"), qed(3)],
        )
        self.assertEqual(0, exit_code)
        self.assertTrue(result["accepted"])
        self.assertEqual([], result["reasons"])

    def test_rejects_axiom_inside_proof(self) -> None:
        result, exit_code = self.run_validator(
            [start(1), tactic(2, "old"), qed(3)],
            [start(1), side_effect(2, "VernacAssumption"), qed(3)],
        )
        self.assertEqual(1, exit_code)
        self.assertIn("PROOF_SIDE_EFFECT", self.codes(result))

    def test_rejects_unset_guard_checking_inside_proof(self) -> None:
        result, _ = self.run_validator(
            [start(1), tactic(2, "old"), qed(3)],
            [start(1), side_effect(2, "VernacSetOption"), qed(3)],
        )
        self.assertIn("PROOF_SYNTERP_FORBIDDEN", self.codes(result))

    def test_rejects_admitted(self) -> None:
        result, _ = self.run_validator(
            [start(1), tactic(2, "old"), qed(3)],
            [start(1), tactic(2, "new"), qed(3, "KeepAxiom")],
        )
        self.assertIn("INVALID_PROOF_END", self.codes(result))

    def test_submission_accepts_unchanged_admitted_scaffold(self) -> None:
        result, exit_code = self.run_validator(
            [start(1), tactic(2, "admit"), qed(3, "KeepAxiom")],
            [start(1), tactic(2, "exact I"), qed(3, "KeepAxiom")],
            default_policy(stage="submission"),
        )
        self.assertEqual(0, exit_code)
        self.assertTrue(result["accepted"])

    def test_submission_rejects_changed_nonstandard_terminator(self) -> None:
        result, _ = self.run_validator(
            [start(1), tactic(2, "admit"), qed(3, "KeepAxiom")],
            [start(1), tactic(2, "exact I"), qed(3, "KeepDefined")],
            default_policy(stage="submission"),
        )
        self.assertIn("INVALID_PROOF_END", self.codes(result))

    def test_submission_accepts_changed_ordinary_qed(self) -> None:
        result, exit_code = self.run_validator(
            [start(1), tactic(2, "admit"), qed(3, "KeepAxiom")],
            [start(1), tactic(2, "exact I"), qed(3)],
            default_policy(stage="submission"),
        )
        self.assertEqual(0, exit_code)
        self.assertTrue(result["accepted"])

    def test_accepts_replacing_original_admitted_with_qed(self) -> None:
        result, exit_code = self.run_validator(
            [start(1), qed(2, "KeepAxiom")],
            [start(1), tactic(2, "new"), qed(3)],
        )
        self.assertEqual(0, exit_code)
        self.assertTrue(result["accepted"])

    def test_accepts_builtin_ltac_when_original_has_no_plugin_nodes(self) -> None:
        result, exit_code = self.run_validator(
            [start(1), qed(2, "KeepAxiom")],
            [start(1), tactic(2, "exact proof_term"), qed(3)],
        )
        self.assertEqual(0, exit_code)
        self.assertTrue(result["accepted"])

    def test_rejects_exterior_modification(self) -> None:
        original_global = record(
            1, "VernacSynPure", "VernacDefinition", "Sideff", payload="original"
        )
        candidate_global = record(
            1, "VernacSynPure", "VernacDefinition", "Sideff", payload="modified"
        )
        result, _ = self.run_validator(
            [original_global, start(2), tactic(3, "old"), qed(4)],
            [candidate_global, start(2), tactic(3, "new"), qed(4)],
        )
        self.assertIn("EXTERIOR_AST_CHANGED", self.codes(result))

    def test_accepts_exact_whitelisted_require_insertion(self) -> None:
        result, exit_code = self.run_validator(
            [start(1), tactic(2, "old"), qed(3)],
            [require_import(1, "ssreflect", "mathcomp"), start(2), tactic(3, "new"), qed(4)],
            default_policy(allowed_requires=frozenset({"mathcomp::ssreflect"})),
        )
        self.assertEqual(0, exit_code)
        self.assertTrue(result["accepted"])
        self.assertEqual(1, len(result["allowed_additions"]))

    def test_rejects_non_whitelisted_require(self) -> None:
        result, _ = self.run_validator(
            [start(1), tactic(2, "old"), qed(3)],
            [require_import(1, "evil"), start(2), tactic(3, "new"), qed(4)],
        )
        self.assertTrue(
            {"EXTERIOR_AST_CHANGED", "EXTERIOR_NODE_ADDED"} & self.codes(result)
        )

    def test_rejects_untrusted_extension_plugin(self) -> None:
        result, _ = self.run_validator(
            [start(1), tactic(2, "old"), qed(3)],
            [start(1), tactic(2, "new", plugin="evil.plugin"), qed(3)],
        )
        self.assertIn("UNTRUSTED_EXTENSION_PLUGIN", self.codes(result))

    def test_rejects_changed_target_declaration(self) -> None:
        result, _ = self.run_validator(
            [start(1, statement="P"), tactic(2, "old"), qed(3)],
            [start(1, statement="False"), tactic(2, "new"), qed(3)],
        )
        self.assertIn("TARGET_DECLARATION_CHANGED", self.codes(result))

    def test_rejects_multiple_changed_proofs(self) -> None:
        original = [
            start(1, "one"), tactic(2, "old-one"), qed(3),
            start(4, "two"), tactic(5, "old-two"), qed(6),
        ]
        candidate = [
            start(1, "one"), tactic(2, "new-one"), qed(3),
            start(4, "two"), tactic(5, "new-two"), qed(6),
        ]
        result, _ = self.run_validator(original, candidate)
        self.assertIn("MULTIPLE_PROOFS_CHANGED", self.codes(result))

    def test_rejects_old_summary_schema_without_raw_ast(self) -> None:
        bad_start = start(1)
        del bad_start["ast"]
        result, _ = self.run_validator(
            [bad_start, tactic(2, "old"), qed(3)],
            [start(1), tactic(2, "new"), qed(3)],
        )
        self.assertIn("CLASSIFIED_AST_SCHEMA_MISMATCH", self.codes(result))


if __name__ == "__main__":
    unittest.main()
