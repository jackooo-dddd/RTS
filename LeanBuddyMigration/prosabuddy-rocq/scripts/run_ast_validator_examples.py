#!/usr/bin/env python3
"""Run fcc, the Rocq classifier, and the AST validator over a case manifest."""

from __future__ import annotations

import argparse
import json
import subprocess
from pathlib import Path
from typing import Any


def run(command: list[str]) -> subprocess.CompletedProcess[str]:
    return subprocess.run(command, text=True, capture_output=True, check=False)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("case_dir", type=Path)
    parser.add_argument("original_classified", type=Path)
    parser.add_argument("classifier", type=Path)
    parser.add_argument("validator", type=Path)
    parser.add_argument("--prosa-root", type=Path, required=True)
    return parser.parse_args()


def write_markdown(path: Path, results: list[dict[str, Any]]) -> None:
    lines = [
        "# AST validator example results",
        "",
        "| # | Case | Expected | Actual | Match | fcc | Classifier | Reasons |",
        "|---:|---|---|---|---|---:|---:|---|",
    ]
    for index, result in enumerate(results, 1):
        reasons = ", ".join(result["reason_codes"]) or "—"
        lines.append(
            f"| {index} | `{result['filename']}` | {result['expected']} | "
            f"{result['actual']} | {'yes' if result['matches_expected'] else 'NO'} | "
            f"{result['fcc_exit']} | {result['classifier_exit']} | {reasons} |"
        )
    lines.extend(
        [
            "",
            f"Matched: {sum(item['matches_expected'] for item in results)}/{len(results)}",
            "",
        ]
    )
    path.write_text("\n".join(lines), encoding="utf-8")


def main() -> int:
    args = parse_args()
    manifest_path = args.case_dir / "manifest.json"
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    results: list[dict[str, Any]] = []

    for case in manifest:
        source = args.case_dir / case["filename"]
        raw_ast = Path(str(source) + ".jsonl.astdump")
        classified = source.with_suffix(source.suffix + ".classified.jsonl")
        verdict_path = source.with_suffix(source.suffix + ".verdict.json")

        fcc = run(
            [
                "fcc",
                "--no_vo",
                "--plugin=coq-lsp.plugin.astdump",
                "-R",
                f"{args.prosa_root},prosa",
                str(source),
            ]
        )
        source.with_suffix(".fcc.stdout").write_text(fcc.stdout, encoding="utf-8")
        source.with_suffix(".fcc.stderr").write_text(fcc.stderr, encoding="utf-8")

        classifier_exit: int | None = None
        validator_exit: int | None = None
        verdict: dict[str, Any] | None = None
        if raw_ast.exists() and raw_ast.stat().st_size > 0:
            classifier = run(
                [str(args.classifier), str(raw_ast), str(classified)]
            )
            classifier_exit = classifier.returncode
            source.with_suffix(".classifier.stdout").write_text(
                classifier.stdout, encoding="utf-8"
            )
            source.with_suffix(".classifier.stderr").write_text(
                classifier.stderr, encoding="utf-8"
            )
            if classified.exists() and classified.stat().st_size > 0:
                command = [
                    "python3",
                    str(args.validator),
                    str(args.original_classified),
                    str(classified),
                    "--target",
                    "Lemma4_09",
                    "--compact",
                ]
                for module in case.get("allowed_requires", []):
                    command.extend(["--allow-require", module])
                validator = run(command)
                validator_exit = validator.returncode
                try:
                    verdict = json.loads(validator.stdout)
                except json.JSONDecodeError:
                    verdict = {
                        "accepted": False,
                        "reasons": [
                            {
                                "code": "INVALID_VALIDATOR_OUTPUT",
                                "message": validator.stdout,
                            }
                        ],
                    }
                verdict_path.write_text(
                    json.dumps(verdict, ensure_ascii=False, indent=2) + "\n",
                    encoding="utf-8",
                )

        accepted = bool(verdict and verdict.get("accepted"))
        actual = "accept" if accepted else "reject"
        all_reason_codes = [
            item.get("code", "<missing>")
            for item in (verdict or {}).get("reasons", [])
        ]
        reason_codes = list(dict.fromkeys(all_reason_codes))
        expected_reason = case.get("expected_reason")
        matches_expected = actual == case["expected"] and (
            expected_reason is None or expected_reason in reason_codes
        )
        results.append(
            {
                **case,
                "actual": actual,
                "matches_expected": matches_expected,
                "reason_codes": reason_codes,
                "reason_count": len(all_reason_codes),
                "fcc_exit": fcc.returncode,
                "classifier_exit": classifier_exit,
                "validator_exit": validator_exit,
                "raw_ast": str(raw_ast),
                "classified": str(classified),
                "verdict": str(verdict_path),
            }
        )

    (args.case_dir / "results.json").write_text(
        json.dumps(results, ensure_ascii=False, indent=2) + "\n",
        encoding="utf-8",
    )
    write_markdown(args.case_dir / "RESULTS.md", results)
    matched = sum(item["matches_expected"] for item in results)
    print(json.dumps({"matched": matched, "total": len(results)}, ensure_ascii=False))
    return 0 if matched == len(results) else 1


if __name__ == "__main__":
    raise SystemExit(main())
