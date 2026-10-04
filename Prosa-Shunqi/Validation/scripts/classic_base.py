#!/usr/bin/env python3
"""Write a re-bound classic validation base module (Booleans, decide bridge, Nat decisions, eqType
instance, statement combinators) for one classic export.

The parts are extracted verbatim from the accepted classic tactics certificate
(certificates/classic_common/classic_base_parts.json); only the imported module name changes.
Features: bool decide boolrel andb orb notb decle declt sub min max eqnat booltonat eqtype logic or forall exists (any subset, in that order).

usage: classic_base.py OUT.v IMPORTED_MODULE feature...
"""
import json
import sys
from pathlib import Path

V = Path(__file__).resolve().parents[1]
ORDER = ["bool", "decide", "boolrel", "andb", "orb", "notb", "decle", "declt", "sub", "min", "max", "eqnat", "booltonat", "eqtype", "logic", "or",
         "forall", "exists"]


def main() -> None:
    out, imported, *features = sys.argv[1:]
    data = json.loads((V / "certificates/classic_common/classic_base_parts.json").read_text())
    unknown = set(features) - set(ORDER) - {"nodecide"}
    if unknown:
        raise SystemExit(f"unknown features {unknown}")
    # the original `bool` feature is `bool decide boolrel`; keep accepting it with that meaning
    if "bool" in features and "nodecide" not in features:
        features = list(features) + ["decide", "boolrel"]
    chosen = [f for f in ORDER if f in features]
    text = data["header"].replace("@IMPORTED@", imported).replace("@FEATURES@", " ".join(chosen))
    text += "".join(data["parts"][f] for f in chosen)
    Path(out).write_text(text)


if __name__ == "__main__":
    main()
