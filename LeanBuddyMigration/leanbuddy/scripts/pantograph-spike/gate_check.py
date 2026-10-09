#!/usr/bin/env python3
"""Phase 1: the D4 gate end to end. `benchmark/check.py` must PASS on a reference solution in a fresh verification
copy and FAIL for `sorry`, an added `axiom`, `native_decide`, and a changed `Statement.lean`.

usage: python3 gate_check.py --master <built package copy> --refs <lean-prosa-v06-reference-solutions> \
           --work <scratch dir> [--task 2005-ECRTS-Lemma3] [--out gate-results.json]
"""
import argparse
import json
import shutil
import subprocess
import time
from pathlib import Path

HERE = Path(__file__).parent


def stage(master, dest):
    subprocess.run(["bash", str(HERE / "stage_copy.sh"), str(master), str(dest)], check=True, capture_output=True)


def check(copy, task_id):
    out = copy / ".lake" / "gate.json"
    t0 = time.time()
    r = subprocess.run(["python3", "benchmark/check.py", task_id, "--json", str(out)], cwd=copy,
                       capture_output=True, text=True)
    secs = time.time() - t0
    try:
        data = json.loads(out.read_text())
    except Exception:
        data = None
    return {"exit": r.returncode, "seconds": round(secs, 1), "json": data, "stdout": r.stdout[-800:]}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--master", required=True)
    ap.add_argument("--refs", required=True)
    ap.add_argument("--work", required=True)
    ap.add_argument("--task", default="2005-ECRTS-Lemma3")
    ap.add_argument("--out", default="gate-results.json")
    a = ap.parse_args()
    master, refs, work = Path(a.master), Path(a.refs), Path(a.work)
    tasks = json.loads((master / "benchmark/tasks.json").read_text())
    task = next(t for t in tasks if t["id"] == a.task)
    sol_rel = task["solution_file"]
    ref = (refs / sol_rel).read_text()
    support = sorted((refs / "CaseStudies/Support").glob("*.lean"))
    work.mkdir(parents=True, exist_ok=True)

    def variant(name, solution_text, statement_edit=None):
        dest = work / name
        if dest.exists():
            shutil.rmtree(dest)
        stage(master, dest)
        (dest / "CaseStudies/Support").mkdir(exist_ok=True)
        for s in support:  # helper modules the agent may add (frozen check allows new files under CaseStudies/)
            shutil.copy(s, dest / "CaseStudies/Support" / s.name)
        (dest / sol_rel).write_text(solution_text)
        if statement_edit:
            p = dest / task["statement_file"]
            p.write_text(statement_edit(p.read_text()))
        res = check(dest, a.task)
        status = next((r for r in (res["json"] or []) if r.get("id") == a.task), None)
        print(f"{name}: exit={res['exit']} {res['seconds']}s {json.dumps(status, ensure_ascii=False)[:300]}")
        return {"status": status, **{k: res[k] for k in ("exit", "seconds", "stdout")}}

    body_start = ref.index("theorem CaseStudies.")  # the final `solution` alias
    nd_helper = ("theorem gate_nd_helper : (2 : Nat) + 2 = 4 := by native_decide\n\n")
    results = {
        "reference": variant("reference", ref),
        "sorry": variant("sorry", ref[:body_start] + ref[body_start:].split(":=")[0] + ":= by\n  sorry\n"),
        "axiom": variant("axiom", ref[:body_start] + "axiom gate_extra : False\n\n" + ref[body_start:]),
        "native_decide": variant("native_decide", ref[:body_start] + nd_helper + ref[body_start:].replace(
            ":=\n", ":= by\n  have _h := gate_nd_helper\n  exact\n", 1)),
        "statement_changed": variant("statement_changed", ref, lambda s: s + "\n-- edited\n"),
    }
    Path(a.out).write_text(json.dumps(results, indent=1, ensure_ascii=False))


if __name__ == "__main__":
    main()
