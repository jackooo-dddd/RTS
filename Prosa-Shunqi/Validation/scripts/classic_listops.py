#!/usr/bin/env python3
"""Write a re-bound classic list library module (sequences against Lean lists) for one classic export.

The parts are extracted verbatim from the accepted certificates/classic_util_list/ClassicListOps.v
(certificates/classic_common/classic_listops_parts.json); only the imported module and base module names change.
Features (any subset; `core` is always included): existslist pair opt size cat mapop filter take nth zip nseq pmap all mem uniq index.

usage: classic_listops.py OUT.v IMPORTED_MODULE BASE_MODULE feature...
"""
import json
import sys
from pathlib import Path

V = Path(__file__).resolve().parents[1]
ORDER = ["core", "existslist", "pair", "opt", "size", "cat", "mapop", "filter", "take", "nth", "zip", "nseq", "pmap", "all", "mem", "uniq", "index"]


def main() -> None:
    out, imported, base, *features = sys.argv[1:]
    data = json.loads((V / "certificates/classic_common/classic_listops_parts.json").read_text())
    unknown = set(features) - set(ORDER)
    if unknown:
        raise SystemExit(f"unknown features {unknown}")
    chosen = [f for f in ORDER if f in features or f == "core"]
    text = data["header"].replace("@IMPORTED@", imported).replace("@BASE@", base).replace("@FEATURES@", " ".join(chosen))
    text += "".join(data["parts"][f] for f in chosen)
    Path(out).write_text(text)


if __name__ == "__main__":
    main()
