#!/usr/bin/env python3
"""(Re)generate reports/<source>.md for every TRANSLATED or ACCEPTED file of file_order.csv.

The declaration list is the authoritative inventory (Validation/planning/classic_dependency/
declaration_inventory.csv, enumerated by Rocq in ProsaBuddy's toolchain); each declaration is
checked to exist in the Lean translation (`<namespace>.<name>`, found as a `def`/`theorem`/... with
the last name component inside the file's namespaces).  Lean-only helpers are the `private`
declarations of the Lean file.  The "History" section of an existing report is kept and extended.

usage: make_reports.py [RANK ...]
"""
import csv
import re
import sys
from datetime import date
from pathlib import Path

HERE = Path(__file__).resolve().parent
PROJECT = HERE.parents[1]
INV = PROJECT / "Validation/planning/classic_dependency/declaration_inventory.csv"


def lean_decls(text: str) -> tuple[set[str], list[str]]:
    """Fully qualified (namespace-relative to the file namespace) public names and private names."""
    names, private, stack = set(), [], []
    for line in text.splitlines():
        m = re.match(r"\s*namespace\s+(\S+)", line)
        if m:
            stack.append(m.group(1)); continue
        m = re.match(r"\s*end\s+(\S+)\s*$", line)
        if m and stack and stack[-1] == m.group(1):
            stack.pop(); continue
        m = re.match(r"\s*(private\s+)?(?:noncomputable\s+)?(?:@\[[^\]]*\]\s*)?"
                     r"(def|theorem|lemma|abbrev|structure|inductive|class|instance)\s+([^\s(:{\[]+)", line)
        if m:
            full = ".".join(stack + [m.group(3)])
            (private.append(m.group(3)) if m.group(1) else names.add(full))
    return names, private


def main() -> None:
    ranks = set(sys.argv[1:])
    order = list(csv.DictReader((HERE / "file_order.csv").open()))
    inv = list(csv.DictReader(INV.open()))
    for r in order:
        if r["status"] not in ("TRANSLATED", "ACCEPTED") or (ranks and r["rank"] not in ranks):
            continue
        src = r["source"]
        lean = PROJECT / r["lean_target"]
        text = lean.read_text()
        public, private = lean_decls(text)
        mod_ns = "Prosa." + ".".join(p[0].upper() + "".join(w.capitalize() for w in p.split("_"))[1:]
                                     for p in src[:-2].split("/"))
        rows = [d for d in inv if d["source_file"] == src]
        missing = [d["declaration_name"] for d in rows if f"{mod_ns}.{d['declaration_name']}" not in public]
        doc = re.search(r"/-!\n(.*?)-/", text, re.S)
        notes = doc.group(1).strip() if doc else "(none)"
        out = HERE / "reports" / (src[:-2].replace("/", "__") + ".md")
        history = []
        if out.exists():
            old = out.read_text()
            if "## History" in old:
                history = [l for l in old.split("## History", 1)[1].strip().splitlines() if l.strip()]
        event = (f"- {date.today().isoformat()}: translated; build and axiom check passed."
                 if r["status"] == "TRANSLATED" else f"- {date.today().isoformat()}: accepted.")
        if event not in history:
            history.append(event)
        lines = [
            f"# Report: `{src}` (rank {r['rank']})", "",
            "| Item | Value |", "|---|---|",
            f"| Source | ProsaBuddy `f692cb7`, `prosaworkspace/{src}` |",
            f"| sha256 | `{r['sha256']}` |",
            f"| Lean module | `{r['lean_target']}` (namespace `{mod_ns}`) |",
            f"| Tier / layer | {r['tier']} / {r['layer']} |",
            "| Status | **TRANSLATED**: compiles (Lean 4.33.1, pinned Mathlib), no `sorry`; `#print axioms` "
            "⊆ {`propext`, `Quot.sound`, `Classical.choice`} |" if r["status"] == "TRANSLATED"
            else "| Status | **ACCEPTED** (classic validation family; see the manifest) |",
            "| Validation | pending (classic validation family, `Validation/tooling/classic/file_specs/`) |"
            if r["status"] == "TRANSLATED" else "| Validation | accepted |",
            "", f"## Declarations ({len(rows)} source → Lean, same names)", "",
            *[f"- `{d['kind']}` `{d['declaration_name']}`" for d in rows], "",
            f"Missing in Lean: {', '.join(f'`{m}`' for m in missing) if missing else 'none'}.",
            "Lean-only helpers (`LEAN_HELPER`, not counted as translated declarations): "
            + (", ".join(f"`{p}`" for p in private) if private else "none") + ".", "",
            "## Representation notes", "", notes, "", "## History", "", *history, "",
        ]
        out.write_text("\n".join(lines))
        print(f"{r['rank']:>3} {src}: {len(rows)} decls, missing {len(missing)}, helpers {len(private)}")


if __name__ == "__main__":
    main()
