#!/usr/bin/env python3
"""usage: set_status.py SOURCE STATUS [NOTE]   (SOURCE like classic/util/find_seq.v); then re-renders the README."""
import csv, sys, subprocess
from pathlib import Path
HERE = Path(__file__).resolve().parent
src, status = sys.argv[1], sys.argv[2]
note = sys.argv[3] if len(sys.argv) > 3 else None
rows = list(csv.DictReader(open(HERE / "file_order.csv")))
hit = [r for r in rows if r["source"] == src]
if not hit:
    sys.exit(f"unknown source {src}")
hit[0]["status"] = status
if note is not None:
    hit[0]["note"] = note
with open(HERE / "file_order.csv", "w", newline="") as fh:
    w = csv.DictWriter(fh, fieldnames=list(rows[0])); w.writeheader(); w.writerows(rows)
subprocess.run([sys.executable, str(HERE / "make_plan.py")], check=True)
