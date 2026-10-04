#!/usr/bin/env python3
"""Check every TRANSLATED (or ACCEPTED) file of file_order.csv:
  1. the Lean target exists and contains no `sorry`/`admit`;
  2. `lake build` of all targets succeeds;
  3. every declaration of each target module depends only on the standard axioms
     (propext, Classical.choice, Quot.sound) -- via Lean's `collectAxioms`.
Usage: check_translated.py [--status TRANSLATED] (default: TRANSLATED)."""
import csv, re, subprocess, sys, tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
PKG = HERE.parents[1]                      # Prosa-Shunqi
status = sys.argv[sys.argv.index("--status") + 1] if "--status" in sys.argv else "TRANSLATED"
rows = [r for r in csv.DictReader(open(HERE / "file_order.csv")) if r["status"] == status]
mods, bad = [], []
for r in rows:
    p = PKG / r["lean_target"]
    if not p.exists():
        bad.append(f"MISSING {r['lean_target']}"); continue
    text = re.sub(r"/-.*?-/|--[^\n]*", "", p.read_text(), flags=re.S)
    if re.search(r"\b(sorry|admit)\b", text):
        bad.append(f"SORRY {r['lean_target']}")
    mods.append(r["lean_target"][:-len(".lean")].replace("/", "."))
print(f"{len(rows)} {status} files")
b = subprocess.run(["lake", "build", *mods], cwd=PKG, capture_output=True, text=True)
if b.returncode != 0:
    print(b.stdout[-4000:], b.stderr[-2000:]); bad.append("BUILD FAILED")
probe = "import " + "\nimport ".join(mods) + """
open Lean Elab Command in
#eval show CommandElabM Unit from do
  let env ← getEnv
  let ok : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mods : List Name := [""" + ", ".join(f"`{m}" for m in mods) + """]
  let mut n : Nat := 0
  for (c, _) in env.constants.toList do
    match env.getModuleIdxFor? c with
    | some idx =>
      if mods.contains (env.header.moduleNames[idx.toNat]!) && !c.isInternal then
        n := n + 1
        let axs ← liftCoreM (collectAxioms c)
        for a in axs do
          if !ok.contains a then logInfo m!"BAD_AXIOM {c} {a}"
    | none => pure ()
  logInfo m!"CHECKED {n} declarations"
"""
with tempfile.NamedTemporaryFile("w", suffix=".lean", dir=PKG / ".lake", delete=False) as f:
    f.write(probe); probe_path = f.name
r = subprocess.run(["lake", "env", "lean", probe_path], cwd=PKG, capture_output=True, text=True)
Path(probe_path).unlink()
out = r.stdout + r.stderr
for line in out.splitlines():
    if "BAD_AXIOM" in line or "CHECKED" in line or "error" in line:
        print(line.strip())
if "BAD_AXIOM" in out or r.returncode != 0:
    bad.append("AXIOM CHECK FAILED")
print("\n".join(bad) if bad else "OK: all targets build, no sorry/admit, only standard axioms")
sys.exit(1 if bad else 0)
