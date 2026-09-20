#!/usr/bin/env python3
"""Compare frozen Lean declaration fingerprints with historical Prosa revisions.

This is a provenance heuristic, not a semantic validator.  It reads each
Lean file's ``Translated from`` comment, extracts public declaration names and
order, and compares them with the indicated path at selected Git revisions.
"""

from __future__ import annotations

import argparse
import csv
import json
import re
import subprocess
from collections import Counter
from pathlib import Path


ROOTS = {"behavior", "util", "model", "analysis", "results"}
COQ_DECL = re.compile(
    r"(?m)^\s*(?:(?:Local|Global)\s+)?(?:Program\s+)?"
    r"(Definition|Lemma|Theorem|Corollary|Fact|Remark|Proposition|Example|"
    r"Fixpoint|CoFixpoint|Inductive|Variant|Record|Structure|Class|Instance|Let)"
    r"\s+([A-Za-z_][A-Za-z0-9_']*)"
)
LEAN_DECL = re.compile(
    r"(?m)^\s*(?:@\[[^\n]*\]\s*)*(?:(?:private|protected|noncomputable|partial|unsafe)\s+)*"
    r"(def|abbrev|theorem|lemma|class|structure|inductive|instance)"
    r"(?:\s+(?:@[A-Za-z_][A-Za-z0-9_'.]*\s*)?)([A-Za-z_][A-Za-z0-9_']*)"
)
SOURCE_COMMENT = re.compile(r"Translated from:\s*(?:\.\./rt-proofs/)?([^\s]+\.v)")


def run(repo: Path, *args: str, check: bool = True) -> str:
    result = subprocess.run(
        ["git", "-C", str(repo), *args], text=True,
        stdout=subprocess.PIPE, stderr=subprocess.PIPE,
    )
    if check and result.returncode:
        raise RuntimeError(result.stderr.strip())
    return result.stdout


def strip_coq_comments(text: str) -> str:
    out: list[str] = []
    depth = 0
    index = 0
    while index < len(text):
        if text.startswith("(*", index):
            depth += 1
            out.extend("  ")
            index += 2
        elif depth and text.startswith("*)", index):
            depth -= 1
            out.extend("  ")
            index += 2
        else:
            char = text[index]
            out.append(char if depth == 0 or char == "\n" else " ")
            index += 1
    return "".join(out)


def strip_lean_comments(text: str) -> str:
    text = re.sub(r"/-(?:.|\n)*?-/", lambda m: "\n" * m.group(0).count("\n"), text)
    return re.sub(r"--[^\n]*", "", text)


def declaration_names(text: str, language: str) -> list[str]:
    stripped = strip_coq_comments(text) if language == "rocq" else strip_lean_comments(text)
    pattern = COQ_DECL if language == "rocq" else LEAN_DECL
    names: list[str] = []
    for match in pattern.finditer(stripped):
        kind, name = match.groups()
        header = match.group(0).lstrip()
        if language == "rocq" and (kind == "Let" or header.startswith("Local ")):
            continue
        if language == "lean" and header.startswith("private "):
            continue
        names.append(name)
    return names


def lcs_length(left: list[str], right: list[str]) -> int:
    row = [0] * (len(right) + 1)
    for x in left:
        previous = 0
        for index, y in enumerate(right, 1):
            saved = row[index]
            if x == y:
                row[index] = previous + 1
            else:
                row[index] = max(row[index], row[index - 1])
            previous = saved
    return row[-1]


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--history-repo", required=True, type=Path)
    parser.add_argument("--lean-root", required=True, type=Path)
    parser.add_argument("--revision", action="append", required=True)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()

    revisions = {
        revision: run(args.history_repo, "rev-parse", f"{revision}^{{commit}}").strip()
        for revision in args.revision
    }
    rows: list[dict[str, object]] = []
    for lean_path in sorted(args.lean_root.rglob("*.lean")):
        relative = lean_path.relative_to(args.lean_root)
        if not relative.parts or relative.parts[0].lower() not in ROOTS:
            continue
        lean_text = lean_path.read_text(errors="replace")
        source_match = SOURCE_COMMENT.search(lean_text)
        if not source_match:
            continue
        source_path = source_match.group(1)
        lean_names = declaration_names(lean_text, "lean")
        for revision, commit in revisions.items():
            object_name = f"{commit}:{source_path}"
            exists = subprocess.run(
                ["git", "-C", str(args.history_repo), "cat-file", "-e", object_name],
                stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
            ).returncode == 0
            rocq_names: list[str] = []
            if exists:
                rocq_names = declaration_names(
                    run(args.history_repo, "show", object_name), "rocq"
                )
            common = (Counter(lean_names) & Counter(rocq_names)).total()
            lcs = lcs_length(lean_names, rocq_names)
            rows.append({
                "lean_file": relative.as_posix(),
                "source_path": source_path,
                "revision": revision,
                "commit": commit,
                "path_exists": exists,
                "lean_count": len(lean_names),
                "rocq_count": len(rocq_names),
                "same_name": common,
                "lcs": lcs,
                "lean_only": sorted((Counter(lean_names) - Counter(rocq_names)).elements()),
                "rocq_only": sorted((Counter(rocq_names) - Counter(lean_names)).elements()),
                "exact_name_sequence": lean_names == rocq_names,
            })

    summary: dict[str, dict[str, int]] = {}
    for revision in revisions:
        selected = [row for row in rows if row["revision"] == revision]
        summary[revision] = {
            "files_with_comment": len(selected),
            "paths_present": sum(bool(row["path_exists"]) for row in selected),
            "exact_name_sequences": sum(bool(row["exact_name_sequence"]) for row in selected),
            "lean_declarations": sum(int(row["lean_count"]) for row in selected),
            "rocq_declarations_at_indicated_paths": sum(int(row["rocq_count"]) for row in selected),
            "same_name_occurrences": sum(int(row["same_name"]) for row in selected),
            "ordered_lcs_occurrences": sum(int(row["lcs"]) for row in selected),
        }

    output = {
        "history_repo": str(args.history_repo.resolve()),
        "lean_root": str(args.lean_root.resolve()),
        "revisions": revisions,
        "summary": summary,
        "files": rows,
        "warning": "Name/order provenance heuristic only; structural conclusions require manual signature inspection.",
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(output, indent=2, sort_keys=True) + "\n")
    csv_path = args.output.with_suffix(".csv")
    with csv_path.open("w", newline="") as stream:
        fields = [
            "lean_file", "source_path", "revision", "commit", "path_exists",
            "lean_count", "rocq_count", "same_name", "lcs", "exact_name_sequence",
            "lean_only", "rocq_only",
        ]
        writer = csv.DictWriter(stream, fieldnames=fields)
        writer.writeheader()
        for row in rows:
            rendered = dict(row)
            rendered["lean_only"] = ";".join(row["lean_only"])
            rendered["rocq_only"] = ";".join(row["rocq_only"])
            writer.writerow(rendered)
    print(json.dumps({"revisions": revisions, "summary": summary}, indent=2))


if __name__ == "__main__":
    main()
