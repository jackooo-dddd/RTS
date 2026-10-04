#!/usr/bin/env python3
"""Compile each RTS_Papers case study (unchanged) against the official-toolchain classic reference build
(Validation/.work/classic_reference_rocq90, opam switch prosa-0.6, Rocq 9.0.1 + MathComp 2.4) and record, for every
declaration of the file, its elaborated type (`Check @M.x`) and, for definitions, its body (`Print M.x`).

usage: cs_contracts.py            -> contracts/<case>.txt, contracts/manifest.json (sha256 of every source)
"""
import csv, hashlib, json, re, shutil, subprocess, tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]                       # TranslationProof/
PAPERS = ROOT / "RTS_Papers"
REF = ROOT / "Prosa-Shunqi/Validation/.work/classic_reference_rocq90/src"
OUT = HERE / "contracts"
# Source defects that stop a case study from compiling in ProsaBuddy's own toolchain, with the minimal repair used to
# obtain its contract (the source file itself is never edited; every repair is recorded in the manifest).
SOURCE_FIXES = {
    "2009-RTSS-Extend1_10": [("uniq [seq fst p <- hp_bounds].", "uniq [seq fst p | p <- hp_bounds].",
                              "line 232: `[seq fst p <- hp_bounds]` is not valid syntax (filter notation without `|`); "
                              "repaired to the map `[seq fst p | p <- hp_bounds]`, as written at the same place in "
                              "2009-RTSS-Method1/Method1_10.v")],
}
DECL = re.compile(r"^\s*(Definition|Fixpoint|Lemma|Theorem|Corollary)\s+([A-Za-z_][\w']*)", re.M)

def modules_of(text):
    # (name, start, end) of every `Module M.` ... `End M.` block
    res = []
    for m in re.finditer(r"^\s*Module\s+([\w]+)\s*\.", text, re.M):
        e = re.search(rf"^\s*End\s+{m.group(1)}\s*\.", text[m.end():], re.M)
        res.append((m.group(1), m.start(), m.end() + (e.start() if e else len(text))))
    return res

def main():
    OUT.mkdir(exist_ok=True)
    manifest = {}
    rows = list(csv.DictReader(open(HERE / "case_studies.csv")))
    for r in rows:
        src = PAPERS / r["file"]
        text = src.read_text()
        fixes = []
        for a, b, why in SOURCE_FIXES.get(r["case_study"], []):
            assert text.count(a) == 1, (r["case_study"], a)
            text = text.replace(a, b); fixes.append(why)
        mods = modules_of(text)
        names = []
        for d in DECL.finditer(text):
            mod = [m for m, s, e in mods if s <= d.start() < e]
            names.append((d.group(1), (mod[-1] + "." if mod else "") + d.group(2)))
        probe = text + "\n\nSet Printing Depth 100000.\n" + "".join(
            f'\nIdtac_marker.\n' if False else f'\nCheck @{n}.\n' + (f'Print {n}.\n' if k in ("Definition", "Fixpoint") else '')
            for k, n in names)
        with tempfile.TemporaryDirectory() as tmp:
            f = Path(tmp) / "CaseStudy.v"
            f.write_text(probe)
            p = subprocess.run(["opam", "exec", "--switch=prosa-0.6", "--", "rocq", "c", "-R", str(REF), "prosa", f.name],
                               cwd=tmp, capture_output=True, text=True)
        out = "\n".join(l for l in (p.stdout + p.stderr).splitlines()
                        if not l.startswith("Warning") and not re.fullmatch(r"\[[\w,\-]+\]", l.strip())
                        and "characters" not in l)
        (OUT / f"{r['case_study']}.txt").write_text(out + "\n")
        manifest[r["case_study"]] = {"file": r["file"], "sha256": hashlib.sha256(src.read_bytes()).hexdigest(),
                                     "compiled": p.returncode == 0, "source_fixes": fixes, "declarations": [n for k, n in names],
                                     "kinds": {n: k for k, n in names}}
        print(r["case_study"], "OK" if p.returncode == 0 else "FAILED", len(names))
    (OUT / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")

if __name__ == "__main__":
    main()
