#!/usr/bin/env python3
"""Regenerate lean/README.md: which RTS_Papers case studies are translated to Lean and which are proved.

A case study is TRANSLATED when its Lean file exists and `lake build` of that module succeeds; it is PROVED
when, in addition, the module contains no `sorry`/`admit` and `#print axioms` of its theorem lists only
`propext`, `Quot.sound`, `Classical.choice` (checked by `lake env lean` on a probe).  A case study whose
statement turned out false is marked DISPROVED (with the Lean counterexample module) instead.
usage: status.py [--no-build]"""
import csv, json, re, subprocess, sys
from pathlib import Path
HERE = Path(__file__).resolve().parent
ROOT = HERE.parent                       # casestudy-translation/
PKG = ROOT.parents[1]                    # Prosa-Shunqi/ (Lake package)
LEAN = ROOT / "lean"
MAN = json.load(open(ROOT / "contracts/manifest.json"))
PATHS = {
    "2005-ECRTS-Lemma3": "ECRTS2005/Lemma3.lean", "2005-ECRTS-Lemma4": "ECRTS2005/Lemma4.lean",
    "2005-ECRTS-Theorem6": "ECRTS2005/Theorem6.lean", "2007-RTSS-Theorem2": "RTSS2007/Theorem2.lean",
    "2007-RTSS-Theorem3": "RTSS2007/Theorem3.lean", "2007-RTSS-Theorem4": "RTSS2007/Theorem4.lean",
    "2009-RTSS-Extend1_10": "RTSS2009/Extend1_10.lean", "2009-RTSS-Lemma1": "RTSS2009/Lemma1.lean",
    "2009-RTSS-Lemma1_2": "RTSS2009/Lemma1_2.lean", "2009-RTSS-Lemma2-1": "RTSS2009/Lemma2_1.lean",
    "2009-RTSS-Lemma2-2": "RTSS2009/Lemma2_2.lean", "2009-RTSS-Lemma3": "RTSS2009/Lemma3.lean",
    "2009-RTSS-Lemma4": "RTSS2009/Lemma4.lean", "2009-RTSS-Lemma5": "RTSS2009/Lemma5.lean",
    "2009-RTSS-Method1": "RTSS2009/Method1.lean", "2009-RTSS-Theorem1": "RTSS2009/Theorem1.lean",
    "2009-RTSS-Theorem2": "RTSS2009/Theorem2.lean", "2014-RTCSA-Lemma4": "RTCSA2014/Lemma4.lean",
    "2014-RTCSA-Lemma5": "RTCSA2014/Lemma5.lean", "2014-RTCSA-Theorem3": "RTCSA2014/Theorem3.lean",
    "2015-BOOK-Lemma18.1": "BOOK2015/Lemma18_1.lean", "2015-RTAS-Lemma8": "RTAS2015/Lemma8.lean",
}
PAPERS = {
    "2005-ECRTS": "Bertogna, Cirinei, Lipari — Improved Schedulability Analysis of EDF on Multiprocessor Platforms (ECRTS 2005)",
    "2007-RTSS": "Bertogna, Cirinei — Response-Time Analysis for Globally Scheduled Symmetric Multiprocessor Platforms (RTSS 2007)",
    "2009-RTSS": "Guan, Stigge, Yi, Yu — New Response Time Bounds for Fixed Priority Multiprocessor Scheduling (RTSS 2009)",
    "2014-RTCSA": "Improving the Response Time Analysis of Global Fixed-Priority Multiprocessor Scheduling (RTCSA 2014)",
    "2015-BOOK": "Baruah, Bertogna, Buttazzo — Multiprocessor Scheduling for Real-Time Systems (book, 2015), Lemma 18.1",
    "2015-RTAS": "Linux push/pull scheduler with arbitrary processor affinities (2015), Lemma 8 (APA)",
}
NOTES = json.load(open(HERE / "status_notes.json")) if (HERE / "status_notes.json").exists() else {}

def module(path): return "CaseStudies." + path[:-5].replace("/", ".")

ALLOWED = {"propext", "Quot.sound", "Classical.choice"}

def theorem_name(text):
    ns = re.search(r"^namespace (\S+)", text, re.M).group(1)
    return ns + "." + re.findall(r"^theorem (\S+)", text, re.M)[-1]

def axioms_ok(path, text):
    """`#print axioms` of the case-study theorem lists only the standard axioms."""
    probe = PKG / ".lake" / "status_axioms_probe.lean"
    probe.write_text(f"import {module(path)}\n#print axioms {theorem_name(text)}\n")
    r = subprocess.run(["lake", "env", "lean", str(probe)], cwd=PKG, capture_output=True, text=True)
    probe.unlink()
    m = re.search(r"depends on axioms: \[(.*?)\]", r.stdout, re.S)
    if r.returncode != 0 or not m:
        return "does not depend on any axioms" in r.stdout
    return {a.strip() for a in m.group(1).split(",")} <= ALLOWED

def main():
    build = "--no-build" not in sys.argv
    rows = []
    for case, path in PATHS.items():
        f = LEAN / "CaseStudies" / path
        translated = proved = False
        state = "not translated"
        if f.exists():
            ok = True
            if build:
                r = subprocess.run(["lake", "build", module(path)], cwd=PKG, capture_output=True, text=True)
                ok = r.returncode == 0
            text = f.read_text()
            code = re.sub(r"--[^\n]*", "", re.sub(r"/-.*?-/", "", text, flags=re.S))
            has_sorry = bool(re.search(r"\b(sorry|admit)\b", code))
            translated = ok
            proved = ok and not has_sorry and (not build or axioms_ok(path, text))
            state = "PROVED" if proved else ("translated (proof pending)" if ok else "translation does not build")
        if case in NOTES and NOTES[case].get("state"):
            state = NOTES[case]["state"]
        rows.append((case, path, translated, proved, state, NOTES.get(case, {}).get("note", "")))
    nt = sum(r[2] for r in rows); npv = sum(r[3] for r in rows)
    lines = [
        "# RTS_Papers case studies in Lean",
        "",
        "Lean 4 translations of the 22 `RTS_Papers` case studies (Rocq statements over ProsaBuddy's classic Prosa,",
        "commit `f692cb7`), stated and proved over this project's Lean classic Prosa (`Prosa.Classic.*`, all 49",
        "files validated against the Rocq reference).  Build: `lake build CaseStudies` from `Prosa-Shunqi/`.",
        "",
        f"**Translated: {nt} / 22 · Proved: {npv} / 22** (generated by `../gen/status.py`; a case study counts as",
        "proved only when its module builds, contains no `sorry`/`admit`, and `#print axioms` of its theorem lists",
        "only `propext`, `Classical.choice`, `Quot.sound`).",
        "",
        "| Case study | Rocq source (`RTS_Papers/`) | Lean module | Translated | Proved | Notes |",
        "|---|---|---|:---:|:---:|---|",
    ]
    for case, path, t, p, state, note in rows:
        lines.append(f"| {case} | `{MAN[case]['file']}` | [`{module(path)}`](CaseStudies/{path}) | "
                     f"{'✅' if t else '—'} | {'✅' if p else ('❌ ' + state if 'DISPROVED' in state else '—')} | {note} |")
    lines += ["", "## Papers", ""] + [f"- **{k}**: {v}" for k, v in PAPERS.items()]
    lines += ["", "## How each case study is proved", "",
              "Hypotheses that a case study states (often earlier lemmas of the paper, e.g. `Lemma1_09`, `H_Lemma2_1`)",
              "are used as given; \"assumed\" below refers to such a hypothesis of the case study itself.", ""]
    lines += [f"- **{case}**: {NOTES.get(case, {}).get('proof', '')}" for case, *_ in rows]
    lines += ["", "Shared proof modules (all proved from the classic Lean Prosa, no new axioms):", "",
              "- [`CaseStudies.Common`](CaseStudies/Common.lean): sums, the FP carry-in scheduling lemma, per-job",
              "  interference/completion facts, interference counting.",
              "- [`CaseStudies.CommonFp`](CaseStudies/CommonFp.lean): the classic Bertogna–Cirinei FP core without the",
              "  response-time recurrence.",
              "- [`CaseStudies.BusyWindow`](CaseStudies/BusyWindow.lean): the 2009 busy-window inequality.",
              "- [`CaseStudies.WorkloadArith`](CaseStudies/WorkloadArith.lean),",
              "  [`CaseStudies.WorkloadJobs`](CaseStudies/WorkloadJobs.lean): sporadic workload bounds (job-level view of",
              "  `workload`, arithmetic of `W_NC` and the carry-in bounds)."]
    lines += ["", "## How the translation is made", "",
              "- Source of truth: each `RTS_Papers/<case>/<file>.v` (sha256 in `../contracts/manifest.json`), compiled",
              "  unchanged against ProsaBuddy's classic Prosa in ProsaBuddy's own toolchain (opam switch `prosa-0.6`);",
              "  the elaborated statement and every local definition are recorded in `../contracts/<case>.txt`",
              "  (`../cs_contracts.py`).  Translations follow those contracts: same binders, order and implicitness;",
              "  representation choices as in the classic representation addendum.",
              "- Source issues are translated as written and listed in the notes column; the only repair is",
              "  `2009-RTSS-Extend1_10`, which does not compile as written (recorded in the manifest).",
              "- The 2009/2014/2015-BOOK files are assembled by `../gen/assemble.py` from one Lean translation per",
              "  distinct Rocq definition variant (`../contracts/variants.json`) and a hand-written theorem.", ""]
    (LEAN / "README.md").write_text("\n".join(lines) + "\n")
    print(f"translated {nt}/22, proved {npv}/22")

if __name__ == "__main__":
    main()
