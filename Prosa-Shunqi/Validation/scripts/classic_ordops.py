#!/usr/bin/env python3
"""Write a re-bound classic ordinal library module for one classic export.

The parts are extracted verbatim from the accepted classic_util_ord_quantifier and classic_util_bigcat certificates
(certificates/classic_common/classic_ordops_parts.json); only the imported module, the interface-theorem prefix and
the dependency modules change.  Features (dependency order is fixed):
  ord ordcov famlist search searchany srcexists srcforall existsrel forallrel bigone big bigcl bigsum bigcat
(bigone only when search is not selected: both define co_one)
(famlist/bigcl/bigcat need a ClassicListOps-style module among DEPS; existsrel/forallrel/bigsum/bigcat need the
interface theorems finRange_any/finRange_all/fin_sum_range'/bigCatFin_range' under IFACE.)

usage: classic_ordops.py OUT.v IMPORTED_MODULE IFACE_PREFIX "DEP MODULES" feature...
"""
import json
import sys
from pathlib import Path

V = Path(__file__).resolve().parents[1]
ORDER = ["ord", "ordcov", "famlist", "search", "searchany", "srcexists", "srcforall", "existsrel", "forallrel",
         "bigone", "big", "bigcl", "bigsum", "bigcat"]


def main() -> None:
    out, imported, iface, deps, *features = sys.argv[1:]
    data = json.loads((V / "certificates/classic_common/classic_ordops_parts.json").read_text())
    unknown = set(features) - set(ORDER)
    if unknown:
        raise SystemExit(f"unknown features {unknown}")
    chosen = [f for f in ORDER if f in features and f in data["parts"]]
    text = (data["header"].replace("@IMPORTED@", imported).replace("@DEPS@", deps)
            .replace("@FEATURES@", " ".join(chosen)))
    text += "".join(data["parts"][f].replace("@IFACE@", "I." + iface) for f in chosen)
    Path(out).write_text(text)


if __name__ == "__main__":
    main()
