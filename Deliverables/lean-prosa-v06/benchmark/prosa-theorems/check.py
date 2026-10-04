#!/usr/bin/env python3
"""Check a solution of one Prosa-theorem task.

usage: python3 benchmark/prosa-theorems/check.py TASK_ID --workdir DIR [--json FILE] [--timeout SECONDS]

Run from the pristine package; DIR is the model's working copy, prepared with prepare.py.  The task PASSES when:

1. Every library file of DIR other than the task's file still has its pristine sha256
   (benchmark/frozen_sha256.json), and no file was added under `Prosa/` or `CaseStudies/`.
2. The task's file differs from the pristine file only inside the proof of the task's theorem: replacing that
   proof by `sorry` gives exactly the prepared file.  (Keep the proof indented below the theorem.)
3. The new proof contains none of the forbidden tokens below (comments are ignored).
4. `lake build <module>` succeeds in DIR.
5. `#print axioms <theorem>` lists only `propext`, `Classical.choice` and `Quot.sound`
   (so no `sorry`, no new axioms, no `native_decide`).
"""
import argparse, hashlib, json, re, subprocess, sys, time
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]                      # the pristine package
sys.dont_write_bytecode = True
sys.path.insert(0, str(HERE))
import holes

ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
FORBIDDEN = [r"\bsorry\b", r"\badmit\b", r"\baxiom\b", r"\bunsafe\b", r"\bimplemented_by\b", r"@\[extern",
             r"\bskipKernelTC\b", r"\baddDeclWithoutChecking\b", r"\bset_option\s+debug\.", r"\brun_cmd\b",
             r"\brun_elab\b", r"\brun_meta\b", r"#eval\b", r"\binitialize\b", r"\belab\b", r"\belab_rules\b"]


def sha256(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


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


def run(cmd, cwd, timeout):
    try:
        r = subprocess.run(cmd, cwd=cwd, capture_output=True, text=True, timeout=timeout)
        return r.returncode, r.stdout + r.stderr
    except subprocess.TimeoutExpired:
        return None, "timeout"


def check(task, work, timeout):
    frozen = json.loads((ROOT / "benchmark" / "frozen_sha256.json").read_text())
    bad = []
    for rel, h in frozen["files"].items():
        if rel == task["lean_file"]:
            continue
        p = work / rel
        if not p.exists():
            bad.append(f"missing: {rel}")
        elif sha256(p) != h:
            bad.append(f"modified: {rel}")
    for tree in frozen["closed_trees"]:
        for p in sorted((work / tree).rglob("*")):
            rel = p.relative_to(work).as_posix()
            if p.is_file() and rel not in frozen["files"] and p.name != ".DS_Store":
                bad.append(f"added: {rel}")
    if bad:
        return "FAIL", "files other than the task's file were changed: " + "; ".join(bad[:10])
    target = work / task["lean_file"]
    if not target.exists():
        return "FAIL", f"{task['lean_file']} is missing"
    text = target.read_text()
    try:
        rehole = holes.hole(text, task["lean_name"])
    except ValueError as e:
        return "FAIL", f"cannot locate the theorem in the edited file: {e}"
    if hashlib.sha256(rehole.encode()).hexdigest() != task["holed_sha256"]:
        return "FAIL", "the file was changed outside the proof of the theorem"
    proof = strip_comments(holes.proof(text, task["lean_name"]))
    hits = sorted({h.group(0) for pat in FORBIDDEN for h in re.finditer(pat, proof)})
    if hits:
        return "FAIL", "forbidden token(s) in the proof: " + ", ".join(hits)
    rc, out = run(["lake", "build", task["lean_module"]], work, timeout)
    if rc != 0:
        tail = "\n".join(l for l in out.splitlines() if "error" in l)[:2000]
        return "FAIL", "build failed" + (" (timeout)" if rc is None else "") + (": " + tail if tail else "")
    probe_dir = work / ".lake" / "benchmark"
    probe_dir.mkdir(parents=True, exist_ok=True)
    probe = probe_dir / (re.sub(r"\W", "_", task["id"]) + ".lean")
    probe.write_text(f"import {task['lean_module']}\n\n#print axioms {task['lean_declaration']}\n")
    rc, out = run(["lake", "env", "lean", str(probe)], work, timeout)
    if rc != 0:
        return "FAIL", "could not query the axioms: " + out.strip()[:1000]
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
    ap.add_argument("task")
    ap.add_argument("--workdir", required=True, help="the model's copy of the package")
    ap.add_argument("--json", help="write the result to this file")
    ap.add_argument("--timeout", type=int, default=3600, help="seconds per lake command (default 3600)")
    args = ap.parse_args()
    tasks = {t["id"]: t for t in json.loads((HERE / "tasks.json").read_text())}
    if args.task not in tasks:
        sys.exit(f"unknown task id {args.task}; see benchmark/prosa-theorems/tasks.json")
    task = tasks[args.task]
    if not task["available"]:
        sys.exit(f"task {args.task} is not available in Lean: {task['note']}")
    work = Path(args.workdir).resolve()
    if work == ROOT:
        sys.exit("--workdir must be the model's copy, not the pristine package")
    t0 = time.time()
    verdict, detail = check(task, work, args.timeout)
    result = {"id": task["id"], "result": verdict, "detail": detail, "seconds": round(time.time() - t0, 1)}
    print(f"{verdict}  {task['id']}  {detail.splitlines()[0] if detail else ''}")
    if args.json:
        Path(args.json).write_text(json.dumps(result, indent=2, ensure_ascii=False) + "\n")
    sys.exit(0 if verdict == "PASS" else 1)


if __name__ == "__main__":
    main()
