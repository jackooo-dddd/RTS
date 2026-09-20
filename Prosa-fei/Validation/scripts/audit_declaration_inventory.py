#!/usr/bin/env python3
"""Public-inventory audit of pinned Prosa Rocq declarations against Lean files.

This deliberately does not claim semantic equivalence.  It supplies a
reproducible exact-name/kind baseline for the manual structural audit.  Rocq
section-local declarations and Lean private helpers are excluded from the
public coverage metric; a broader pass can be retained separately when needed.
"""

from __future__ import annotations

import argparse
import csv
import json
import re
from collections import Counter
from pathlib import Path


ROOTS = ("behavior", "util", "model", "analysis", "results")
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


def strip_coq_comments(text: str) -> str:
    out: list[str] = []
    depth = 0
    i = 0
    while i < len(text):
        if text.startswith("(*", i):
            depth += 1
            out.extend("  ")
            i += 2
        elif depth and text.startswith("*)", i):
            depth -= 1
            out.extend("  ")
            i += 2
        else:
            ch = text[i]
            out.append(ch if depth == 0 or ch == "\n" else " ")
            i += 1
    return "".join(out)


def strip_lean_comments(text: str) -> str:
    # Preserve line count and declaration headers; sufficient for this audit.
    text = re.sub(r"/-(?:.|\n)*?-/", lambda m: "\n" * m.group(0).count("\n"), text)
    return re.sub(r"--[^\n]*", "", text)


def declarations(path: Path, language: str) -> list[dict[str, object]]:
    raw = path.read_text(errors="replace")
    text = strip_coq_comments(raw) if language == "rocq" else strip_lean_comments(raw)
    pattern = COQ_DECL if language == "rocq" else LEAN_DECL
    result = []
    for match in pattern.finditer(text):
        line = text.count("\n", 0, match.start()) + 1
        kind, name = match.groups()
        header = match.group(0).lstrip()
        # This audit compares the public declaration inventory.  Section-local
        # Rocq Lets/Local declarations and Lean private helpers are
        # implementation details, not missing/extra public API declarations.
        if language == "rocq" and (kind == "Let" or header.startswith("Local ")):
            continue
        if language == "lean" and header.startswith("private "):
            continue
        # Anonymous Lean instances have no stable user declaration name and do
        # not match this regex.  Generated constructors/recursors are likewise
        # absent because only source-level headers are scanned.
        result.append({"name": name, "kind": kind, "line": line})
    return result


def relative_files(root: Path, suffix: str) -> dict[str, Path]:
    files: dict[str, Path] = {}
    for family in ROOTS:
        base = root / family
        if not base.exists():
            # Lean directories are capitalized.
            base = root / family.capitalize()
        if not base.exists():
            continue
        for path in base.rglob(f"*{suffix}"):
            rel = path.relative_to(root).as_posix().lower()
            rel = rel[: -len(suffix)]
            files[rel] = path
    return files


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--rocq-root", required=True, type=Path)
    parser.add_argument("--lean-root", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()

    rocq_files = relative_files(args.rocq_root, ".v")
    lean_files = relative_files(args.lean_root, ".lean")
    keys = sorted(set(rocq_files) | set(lean_files))
    rows = []
    anomalies = []
    totals = Counter()

    for key in keys:
        rp, lp = rocq_files.get(key), lean_files.get(key)
        rdecls = declarations(rp, "rocq") if rp else []
        ldecls = declarations(lp, "lean") if lp else []
        rcounts = Counter(d["name"] for d in rdecls)
        lcounts = Counter(d["name"] for d in ldecls)
        direct = rcounts & lcounts
        missing = rcounts - lcounts
        extra = lcounts - rcounts
        totals.update(rocq=len(rdecls), lean=len(ldecls), direct=direct.total(),
                      missing=missing.total(), extra=extra.total())
        rows.append({
            "file": key + ".v",
            "lean_file": (str(lp.relative_to(args.lean_root)) if lp else None),
            "rocq_count": len(rdecls), "lean_count": len(ldecls),
            "direct": direct.total(), "missing": missing.total(), "extra": extra.total(),
            "rocq_file_present": rp is not None, "lean_file_present": lp is not None,
        })
        rby: dict[str, list[dict[str, object]]] = {}
        lby: dict[str, list[dict[str, object]]] = {}
        for declaration in rdecls:
            rby.setdefault(str(declaration["name"]), []).append(declaration)
        for declaration in ldecls:
            lby.setdefault(str(declaration["name"]), []).append(declaration)
        for name in sorted(set(rcounts) | set(lcounts)):
            paired = min(rcounts[name], lcounts[name])
            for index in range(paired):
                anomalies.append({"file": key + ".v", "rocq": rby[name][index],
                                  "lean": lby[name][index], "baseline": "DIRECT_MATCH"})
            for declaration in rby.get(name, [])[paired:]:
                anomalies.append({"file": key + ".v", "rocq": declaration,
                                  "lean": None, "baseline": "ROCQ_MISSING_IN_LEAN"})
            for declaration in lby.get(name, [])[paired:]:
                anomalies.append({"file": key + ".v", "rocq": None,
                                  "lean": declaration, "baseline": "LEAN_EXTRA"})

    global_rocq: dict[str, list[str]] = {}
    global_lean: dict[str, list[str]] = {}
    for item in anomalies:
        if item["rocq"]:
            declaration = item["rocq"]
            global_rocq.setdefault(str(declaration["name"]), []).append(
                f'{item["file"]}:{declaration["line"]}:{declaration["kind"]}')
        if item["lean"]:
            declaration = item["lean"]
            global_lean.setdefault(str(declaration["name"]), []).append(
                f'{item["file"]}:{declaration["line"]}:{declaration["kind"]}')
    global_name_pairs = sum(
        min(len(global_rocq.get(name, [])), len(global_lean.get(name, [])))
        for name in set(global_rocq) | set(global_lean)
    )
    global_pairing = {
        "same_name_pairs_any_file": global_name_pairs,
        "additional_cross_file_same_name_pairs_upper_bound":
            global_name_pairs - totals["direct"],
        "rocq_occurrences_without_same_name_lean": totals["rocq"] - global_name_pairs,
        "lean_occurrences_without_same_name_rocq": totals["lean"] - global_name_pairs,
        "minimum_rocq_occurrences_without_any_one_to_one_slot":
            max(0, totals["rocq"] - totals["lean"]),
    }
    result = {
        "scope": list(ROOTS),
        "rocq_root": str(args.rocq_root.resolve()),
        "lean_root": str(args.lean_root.resolve()),
        "totals": dict(totals),
        "global_name_pairing": global_pairing,
        "file_counts": {"rocq": len(rocq_files), "lean": len(lean_files),
                        "union": len(keys)},
        "files": rows,
        "declarations": anomalies,
        "note": "Exact source-level header inventory only; manual classifications may override baseline.",
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    with args.output.with_name("file_summary.csv").open("w", newline="") as stream:
        fields = ["file", "lean_file", "rocq_count", "lean_count", "direct",
                  "missing", "extra", "rocq_file_present", "lean_file_present"]
        writer = csv.DictWriter(stream, fieldnames=fields)
        writer.writeheader()
        writer.writerows({key: row[key] for key in fields} for row in rows)
    with args.output.with_name("declaration_inventory.csv").open("w", newline="") as stream:
        fields = ["rocq_file", "rocq_declaration", "rocq_kind", "rocq_line",
                  "lean_declaration", "lean_kind", "lean_line", "baseline",
                  "same_name_lean_candidates", "same_name_rocq_candidates"]
        writer = csv.DictWriter(stream, fieldnames=fields)
        writer.writeheader()
        for item in anomalies:
            rd, ld = item["rocq"], item["lean"]
            writer.writerow({
                "rocq_file": item["file"],
                "rocq_declaration": rd["name"] if rd else "",
                "rocq_kind": rd["kind"] if rd else "",
                "rocq_line": rd["line"] if rd else "",
                "lean_declaration": ld["name"] if ld else "",
                "lean_kind": ld["kind"] if ld else "",
                "lean_line": ld["line"] if ld else "",
                "baseline": item["baseline"],
                "same_name_lean_candidates": ";".join(
                    global_lean.get(str(rd["name"]), [])) if rd else "",
                "same_name_rocq_candidates": ";".join(
                    global_rocq.get(str(ld["name"]), [])) if ld else "",
            })
    print(json.dumps({"file_counts": result["file_counts"], "totals": result["totals"],
                      "global_name_pairing": global_pairing}, indent=2))


if __name__ == "__main__":
    main()
