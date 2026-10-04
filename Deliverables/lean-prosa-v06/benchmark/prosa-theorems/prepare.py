#!/usr/bin/env python3
"""Prepare a working copy of the package for one Prosa-theorem task.

usage: python3 benchmark/prosa-theorems/prepare.py TASK_ID --workdir DIR

Run this script from the pristine package (the one that contains it); DIR is a separate copy of the package that
the model will work in.  The script

1. restores every library file of DIR (everything listed in benchmark/frozen_sha256.json) from the pristine
   package if it differs, and removes files added under `Prosa/` or `CaseStudies/`, so that work from an earlier
   task does not carry over;
2. replaces the proof of the task's theorem in DIR by `sorry` (statement and the rest of the file unchanged);
3. deletes DIR's compiled files of that module (`.lake/build/**/<Module>.*`), which contain the original proof.

The model must then complete the proof in place, editing only the proof of that theorem.  It may use every
declaration the file can see (its imports and the declarations above the theorem), as in ProsaBuddy, where the
theorem's proof is removed from its own Rocq file.  Never give the model access to the pristine package: it
contains the original proofs.
"""
import argparse, hashlib, json, shutil, sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]                      # the pristine package
sys.dont_write_bytecode = True
sys.path.insert(0, str(HERE))
import holes


def sha256(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def load_task(task_id):
    tasks = {t["id"]: t for t in json.loads((HERE / "tasks.json").read_text())}
    if task_id not in tasks:
        sys.exit(f"unknown task id {task_id}; see benchmark/prosa-theorems/tasks.json")
    task = tasks[task_id]
    if not task["available"]:
        sys.exit(f"task {task_id} is not available in Lean: {task['note']}")
    return task


def restore_library(work):
    frozen = json.loads((ROOT / "benchmark" / "frozen_sha256.json").read_text())
    restored = []
    for rel, h in frozen["files"].items():
        dst = work / rel
        if not dst.exists() or sha256(dst) != h:
            dst.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(ROOT / rel, dst)
            restored.append(rel)
    for tree in frozen["closed_trees"]:
        for p in sorted((work / tree).rglob("*")):
            rel = p.relative_to(work).as_posix()
            if p.is_file() and rel not in frozen["files"] and p.name != ".DS_Store":
                p.unlink()
                restored.append(f"removed {rel}")
    return restored


def delete_build_outputs(work, module):
    rel = module.replace(".", "/")
    gone = []
    for sub in ["lib/lean", "ir"]:
        base = work / ".lake" / "build" / sub / rel
        for p in sorted(base.parent.glob(base.name + ".*")) if base.parent.exists() else []:
            if p.is_file():
                p.unlink(); gone.append(p.relative_to(work).as_posix())
    return gone


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("task")
    ap.add_argument("--workdir", required=True, help="the model's copy of the package")
    args = ap.parse_args()
    task = load_task(args.task)
    work = Path(args.workdir).resolve()
    if work == ROOT:
        sys.exit("--workdir must be a separate copy of the package, not the pristine package itself")
    if not (work / "lakefile.lean").exists():
        sys.exit(f"{work} does not look like a copy of the package (no lakefile.lean)")
    restored = restore_library(work)
    target = work / task["lean_file"]
    text = (ROOT / task["lean_file"]).read_text()
    holed = holes.hole(text, task["lean_name"])
    if hashlib.sha256(holed.encode()).hexdigest() != task["holed_sha256"]:
        sys.exit("internal error: the holed file does not match tasks.json")
    target.write_text(holed)
    gone = delete_build_outputs(work, task["lean_module"])
    print(f"task        {task['id']}  ({task['split']}, level {task['level']})")
    print(f"file        {task['lean_file']}")
    print(f"theorem     {task['lean_declaration']}")
    print(f"rocq        {task['rocq_file']} : {task['rocq_theorem']}")
    print(f"restored    {len(restored)} library file(s); deleted {len(gone)} build file(s) of {task['lean_module']}")
    print(f"build with  lake build {task['lean_module']}")


if __name__ == "__main__":
    main()
