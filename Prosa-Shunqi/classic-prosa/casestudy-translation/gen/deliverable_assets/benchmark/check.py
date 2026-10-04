#!/usr/bin/env python3
"""Check solutions of the case-study benchmark.

usage: python3 benchmark/check.py [TASK_ID ...] [--json FILE] [--timeout SECONDS]

With no TASK_ID, every task in benchmark/tasks.json is checked.  A task PASSES when all of these hold:

1. No file outside `Solutions/` was changed: every file listed in benchmark/frozen_sha256.json still has its
   recorded sha256, and no file was added under `Prosa/` or `CaseStudies/`.
2. The solution file exists, and neither it nor any `Solutions.*` module it imports contains one of the
   forbidden tokens below (comments are ignored).
3. `lake build <solution module>` succeeds.
4. A fresh Lean file that imports the statement module and the solution module elaborates
       theorem check : <statement> := <solution>
   i.e. the solution proves exactly the frozen statement, and `#print axioms check` lists only
   `propext`, `Classical.choice` and `Quot.sound` (so no `sorry`, no new axioms, no `native_decide`).
"""
import argparse, hashlib, json, re, subprocess, sys, time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
BENCH = ROOT / "benchmark"
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
# Tokens that could bypass the kernel or hide unchecked code; rejected anywhere in a solution file.
FORBIDDEN = [r"\bsorry\b", r"\badmit\b", r"\baxiom\b", r"\bunsafe\b", r"\bimplemented_by\b", r"@\[extern",
             r"\bskipKernelTC\b", r"\baddDeclWithoutChecking\b", r"\bset_option\s+debug\.", r"\brun_cmd\b",
             r"\brun_elab\b", r"\brun_meta\b", r"#eval\b", r"\binitialize\b", r"\belab\b", r"\belab_rules\b"]


def sha256(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def frozen_violations():
    frozen = json.loads((BENCH / "frozen_sha256.json").read_text())
    bad = []
    for rel, h in frozen["files"].items():
        p = ROOT / rel
        if not p.exists():
            bad.append(f"missing: {rel}")
        elif sha256(p) != h:
            bad.append(f"modified: {rel}")
    for tree in frozen["closed_trees"]:
        for p in sorted((ROOT / tree).rglob("*")):
            rel = p.relative_to(ROOT).as_posix()
            if p.is_file() and rel not in frozen["files"] and p.name != ".DS_Store":
                bad.append(f"added: {rel}")
    return bad


def strip_comments(text):
    out, i, depth = [], 0, 0
    while i < len(text):
        if text.startswith("/-", i):
            depth += 1; i += 2; continue
        if depth and text.startswith("-/", i):
            depth -= 1; i += 2; continue
        if depth:
            i += 1; continue
        if text.startswith("--", i):
            j = text.find("\n", i)
            i = len(text) if j < 0 else j
            continue
        out.append(text[i]); i += 1
    return "".join(out)


def run(cmd, timeout):
    try:
        r = subprocess.run(cmd, cwd=ROOT, capture_output=True, text=True, timeout=timeout)
        return r.returncode, r.stdout + r.stderr
    except subprocess.TimeoutExpired:
        return None, "timeout"


def solutions_closure(module):
    """The `Solutions.*` modules imported (transitively) by `module`, including itself."""
    seen, todo = [], [module]
    while todo:
        m = todo.pop()
        if m in seen:
            continue
        seen.append(m)
        p = ROOT / (m.replace(".", "/") + ".lean")
        if p.exists():
            todo += re.findall(r"^import\s+(Solutions\.\S+)", strip_comments(p.read_text()), re.M)
    return seen


def check_task(task, timeout):
    sol = ROOT / task["solution_file"]
    if not sol.exists():
        return "FAIL", "solution file missing"
    for m in solutions_closure(task["solution_module"]):
        p = ROOT / (m.replace(".", "/") + ".lean")
        if not p.exists():
            continue
        code = strip_comments(p.read_text())
        hits = sorted({h.group(0) for pat in FORBIDDEN for h in re.finditer(pat, code)})
        if hits:
            return "FAIL", f"forbidden token(s) in {p.relative_to(ROOT)}: " + ", ".join(hits)
    rc, out = run(["lake", "build", task["solution_module"]], timeout)
    if rc != 0:
        tail = "\n".join(l for l in out.splitlines() if "error" in l)[:2000]
        return "FAIL", "build failed" + (" (timeout)" if rc is None else "") + (": " + tail if tail else "")
    us = task["universes"]
    uni = ".{" + ", ".join(us) + "}" if us else ""
    probe_dir = ROOT / ".lake" / "benchmark"
    probe_dir.mkdir(parents=True, exist_ok=True)
    probe = probe_dir / (re.sub(r"\W", "_", task["id"]) + ".lean")
    probe.write_text(
        f"import {task['statement_module']}\nimport {task['solution_module']}\n\n"
        + f"theorem benchmark_check{uni} : {task['statement']}{uni} := {task['solution']}\n\n"
        + "#print axioms benchmark_check\n")
    rc, out = run(["lake", "env", "lean", str(probe)], timeout)
    if rc != 0:
        return "FAIL", "the solution does not prove the frozen statement: " + out.strip()[:2000]
    m = re.search(r"depends on axioms: \[(.*?)\]", out, re.S)
    axioms = set() if "does not depend on any axioms" in out else (
        {a.strip() for a in m.group(1).split(",")} if m else None)
    if axioms is None:
        return "FAIL", "could not read the axioms: " + out.strip()[:500]
    extra = sorted(axioms - ALLOWED_AXIOMS)
    if extra:
        return "FAIL", "uses non-standard axioms: " + ", ".join(extra)
    return "PASS", "axioms: " + (", ".join(sorted(axioms)) or "none")


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("tasks", nargs="*", help="task ids (default: all)")
    ap.add_argument("--json", help="write the results to this file")
    ap.add_argument("--timeout", type=int, default=3600, help="seconds per lake command (default 3600)")
    args = ap.parse_args()
    tasks = json.loads((BENCH / "tasks.json").read_text())
    by_id = {t["id"]: t for t in tasks}
    unknown = [t for t in args.tasks if t not in by_id]
    if unknown:
        sys.exit(f"unknown task id(s): {', '.join(unknown)}; see benchmark/tasks.json")
    selected = [by_id[t] for t in args.tasks] if args.tasks else tasks
    violations = frozen_violations()
    results = []
    for task in selected:
        t0 = time.time()
        if violations:
            verdict, detail = "FAIL", "files outside Solutions/ were changed: " + "; ".join(violations[:10])
        else:
            verdict, detail = check_task(task, args.timeout)
        results.append({"id": task["id"], "result": verdict, "detail": detail,
                        "seconds": round(time.time() - t0, 1)})
        print(f"{verdict}  {task['id']}  {detail.splitlines()[0] if detail else ''}", flush=True)
    passed = sum(r["result"] == "PASS" for r in results)
    print(f"\n{passed}/{len(results)} passed")
    if args.json:
        Path(args.json).write_text(json.dumps(results, indent=2, ensure_ascii=False) + "\n")
    sys.exit(0 if passed == len(results) else 1)


if __name__ == "__main__":
    main()
