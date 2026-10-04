#!/usr/bin/env python3
"""Add ProsaBuddy's Prosa-theorem benchmark (65 training + 65 test theorems) to an exported `lean-prosa-v06` package.

usage: theorem_benchmark.py PACKAGE_DIR

* Task list: `deliverable_assets/prosa_theorems/prosabuddy_dataset.csv`, transcribed from ProsaBuddy's
  `train_and_test_data.pdf` (commit f692cb7; split, level, Rocq file, Rocq theorem, in the table's order).
* Each Rocq theorem is mapped to its Lean theorem through the accepted validation manifests
  (Validation/planning/{v06,classic}_pipeline): the declaration record whose source file and name match.  The Lean
  file in PACKAGE_DIR must be byte-identical to the workspace file named by the manifest.
* Writes PACKAGE_DIR/benchmark/prosa-theorems/: tasks.json, the dataset CSV and PDF, holes.py, prepare.py,
  check.py, README.md, PROMPT.md.
"""
import csv, glob, hashlib, json, re, shutil, sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
WS = HERE.parents[2]                                   # Prosa-Shunqi
ASSETS = HERE / "deliverable_assets" / "prosa_theorems"
PB = WS / "Validation/.work/prosabuddy-f692cb7"
sys.dont_write_bytecode = True
sys.path.insert(0, str(ASSETS))
import holes

# entries of ProsaBuddy's table without a Lean declaration of their own: (rocq file, theorem) -> explanation.
# (Empty since 2026-10-04: `job_arrival_is_bounded` of bounded_bi/jlfp.v, a source-`Local` lemma, became a Lean
# theorem certified by amendment 1 of that file.)
NOTES: dict[tuple[str, str], str] = {}


def sha(b):
    return hashlib.sha256(b).hexdigest()


def manifest_index():
    idx = {}
    for f in glob.glob(str(WS / "Validation/planning/v06_pipeline/*manifest*.json")) + \
             glob.glob(str(WS / "Validation/planning/classic_pipeline/*manifest*.json")):
        try:
            d = json.load(open(f))
        except Exception:
            continue
        if not isinstance(d, dict):
            continue
        for x in d.get("declarations") or []:
            if not isinstance(x, dict) or "lean_declaration" not in x:
                continue
            sd = x.get("source_declaration") or x.get("rocq_declaration")
            if not sd:
                continue
            key = (x.get("source_file") or d.get("source_file"), sd.split(".")[-1])
            idx.setdefault(key, set()).add((x["lean_declaration"], x.get("lean_file") or d.get("production_file"),
                                            str(x.get("acceptance", ""))))
    return idx


def main():
    out = Path(sys.argv[1]).resolve()
    dest = out / "benchmark" / "prosa-theorems"
    dest.mkdir(parents=True, exist_ok=True)
    idx = manifest_index()
    rows = list(csv.DictReader(open(ASSETS / "prosabuddy_dataset.csv")))
    tasks, seen, counters = [], {}, {}
    for r in rows:
        counters[r["split"]] = counters.get(r["split"], 0) + 1
        tid = f"{r['split']}-{counters[r['split']]:02d}"
        rel = re.sub(r"^prosa/(rt-proofs-v0\.6/)?", "", r["rocq_file"])
        th = r["rocq_theorem"]
        src = PB / "prosaworkspace/rt-proofs-v0.6" / rel
        if not src.exists():
            src = PB / "prosaworkspace" / rel
        m = re.search(r"((?:Local\s+)?(?:Lemma|Theorem|Corollary|Remark|Fact|Proposition))\s+" + re.escape(th)
                      + r"(?![\w'])", src.read_text())
        if not m:
            raise SystemExit(f"{tid}: {th} not found in {rel}")
        task = dict(id=tid, split=r["split"], level=int(r["level"]), rocq_file=r["rocq_file"], rocq_theorem=th,
                    rocq_kind=m.group(1), available=False, note="", lean_file=None, lean_module=None,
                    lean_declaration=None, lean_name=None, statement=None, holed_sha256=None, proof_lines=None)
        notes = []
        if r["rocq_file"].startswith("prosa/rt-proofs-v0.6/"):
            notes.append("Listed in ProsaBuddy's table under `prosa/rt-proofs-v0.6/`; same file as "
                         f"`prosa/{rel}`.")
        if (rel, th) in seen:
            notes.append(f"Listed twice in ProsaBuddy's table; same theorem as {seen[(rel, th)]}.")
        seen.setdefault((rel, th), tid)
        hits = {h for h in idx.get((rel, th), set()) if h[2].startswith("ACCEPTED")}
        if (rel, th) in NOTES:
            notes.insert(0, NOTES[(rel, th)])
        elif len({h[0] for h in hits}) != 1:
            raise SystemExit(f"{tid}: no unique accepted Lean declaration for {rel} {th}: {sorted(hits)}")
        else:
            decl, lean_file, _ = sorted(hits)[0]
            pkg_file = out / lean_file
            if pkg_file.read_bytes() != (WS / lean_file).read_bytes():
                raise SystemExit(f"{tid}: {lean_file} in the package differs from the accepted workspace file")
            text = pkg_file.read_text()
            name = decl.split(".")[-1]
            task.update(available=True, lean_file=lean_file,
                        lean_module=lean_file[:-len(".lean")].replace("/", "."), lean_declaration=decl,
                        lean_name=name, statement=holes.statement(text, name),
                        holed_sha256=sha(holes.hole(text, name).encode()),
                        proof_lines=holes.proof(text, name).strip().count("\n") + 1)
        task["note"] = " ".join(notes)
        tasks.append(task)
    (dest / "tasks.json").write_text(json.dumps(tasks, indent=1, ensure_ascii=False) + "\n")
    for f in ["holes.py", "prepare.py", "check.py", "README.md", "PROMPT.md", "prosabuddy_dataset.csv"]:
        shutil.copy2(ASSETS / f, dest / f)
    shutil.copy2(PB / "train_and_test_data.pdf", dest / "prosabuddy_train_and_test_data.pdf")
    avail = sum(t["available"] for t in tasks)
    print(f"prosa-theorems: {len(tasks)} tasks, {avail} available in Lean")


if __name__ == "__main__":
    main()
