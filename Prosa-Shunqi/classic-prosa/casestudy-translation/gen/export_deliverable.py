#!/usr/bin/env python3
"""Export the standalone Lean package `lean-prosa-v06` (Prosa v0.6 + classic Prosa + the 23 case studies as a
proof benchmark + ProsaBuddy's Prosa-theorem benchmark, see theorem_benchmark.py) and, separately, the reference
solutions.

usage: export_deliverable.py OUT_PACKAGE_DIR OUT_REFERENCE_DIR OLD_PACKAGE_DIR

* Library: every `Prosa/**/*.lean` of the workspace whose current sha256 is recorded in its own accepted
  validation record (Validation/planning/{v06,classic}_pipeline); files are copied byte-identically.
* One folder per task, `CaseStudies/<G>/<F>/`:
  - `Statement.lean`: the case study's definitions and, instead of the theorem, the closed proposition
    `<thm>_statement : Prop` (read-only for the benchmark);
  - `proof.tex`: the paper's statement and proof sketch, copied from `RTS_Papers/<case>/proof.tex` when it
    exists (read-only hint);
  - `Solution.lean`: a template `theorem solution : <thm>_statement := by sorry`.
* Reference solutions (OUT_REFERENCE_DIR/CaseStudies/<G>/<F>/Solution.lean): the proofs of this workspace,
  restated against the frozen statement modules, plus the shared support modules (`CaseStudies/Support/*`).
"""
import hashlib, json, re, shutil, subprocess, sys, glob, os
from pathlib import Path

HERE = Path(__file__).resolve().parent
CST = HERE.parent                         # classic-prosa/casestudy-translation
WS = CST.parents[1]                       # Prosa-Shunqi
LEAN = CST / "lean"
PAPERS_DIR = WS.parent / "RTS_Papers"
HINT = "proof.tex"
sys.path.insert(0, str(HERE))
import status                              # PATHS, PAPERS, NOTES
import cases as CASEMOD

SUPPORT = ["Common", "CommonFp", "BusyWindow", "WorkloadArith", "WorkloadJobs"]
SUPPORT_RE = re.compile(r"CaseStudies\.(" + "|".join(sorted(SUPPORT, key=len, reverse=True)) + r")\b")
# imports that were added to hand-written case-study files only for their proofs
PROOF_ONLY_IMPORTS = {
    "import Prosa.Classic.Analysis.Global.Basic.WorkloadBound",
    "import Prosa.Classic.Analysis.Apa.BertognaFpTheory",
}

# notes shown to benchmark users: source issues only, nothing about the proofs
NOTE_OVERRIDES = {
    "2005-ECRTS-Theorem6": "Stated as an equivalence (schedulable ⟺ condition), whereas the paper's Theorem 6 is "
                           "a sufficient test; translated as written.",
}

def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()

# ---------------------------------------------------------------- library selection
def accepted_library_files():
    recorded = {}
    for f in glob.glob(str(WS / "Validation/planning/v06_pipeline/*.json")) + \
             glob.glob(str(WS / "Validation/planning/classic_pipeline/*.json")):
        recorded[f] = Path(f).read_text()
    ev = json.load(open(WS / "Validation/planning/v06_pipeline/reports_readme_completion_evidence.json"))["files"]
    out = []
    for p in sorted(glob.glob(str(WS / "Prosa/**/*.lean"), recursive=True)):
        rel = os.path.relpath(p, WS)
        h = sha(p)
        text = Path(p).read_text()
        ok = False
        # accepted module manifest naming the file with its current source hash
        for f, s in recorded.items():
            if f.endswith("_manifest.json") and f'"{rel}"' in s and h in s:
                m = json.loads(s)
                if str(m.get("acceptance", "")).startswith("ACCEPTED") or "ACCEPTED" in recorded.get(
                        f.replace("_manifest.json", "_status.json"), ""):
                    ok = True; break
        if not ok:
            # early files: the status file named by the completion evidence, and its manifest
            src = re.search(r"source: (\S+\.v)", text[:800])
            e = ev.get(src.group(1)) if src else None
            if e:
                st = WS / e["status_file"]
                cands = [st, Path(str(st).replace("_status.json", "_manifest.json"))]
                cands += [Path(f) for f in recorded if Path(f).stem.startswith(st.stem.replace("_status", ""))]
                ok = sha(st) == e["status_sha256"] and any(c.exists() and h in c.read_text() for c in cands)
        if not ok:
            raise SystemExit(f"not verified as accepted: {rel}")
        out.append(rel)
    return out

# ---------------------------------------------------------------- Lean text helpers
def split_signature(sig):
    """`sig` starts right after the theorem name; returns (binders, conclusion, rest-from-:=)."""
    depth = 0; colon = None; i = 0
    while i < len(sig):
        c = sig[i]
        if c in "([{⦃": depth += 1
        elif c in ")]}⦄": depth -= 1
        elif depth == 0 and sig.startswith(":=", i):
            assert colon is not None
            return sig[:colon], sig[colon + 1:i], sig[i:]
        elif depth == 0 and c == ":" and colon is None:
            colon = i
        i += 1
    raise ValueError("no := found")

def last_theorem(text):
    ms = list(re.finditer(r"^theorem (\S+)", text, re.M))
    return ms[-1]

BINDER_SENTENCES = {
    "Binder lists follow the Rocq contracts in `classic-prosa/casestudy-translation/contracts/` (Rocq abstracts "
    "exactly the section variables a declaration uses; a theorem abstracts every variable and hypothesis declared "
    "before it, so some binders are unused).":
        "Binder lists follow the Rocq original: a definition abstracts exactly the section variables it uses, a "
        "theorem every variable and hypothesis declared before it, so some binders are unused.",
    "Binder list as in the Rocq contract (`Check @ResponseTimeAnalysisFP.theorem_2` in ProsaBuddy's toolchain): "
    "every section variable declared before the theorem is abstracted, so the unused task parameters, "
    "`job_deadline` and `arr_seq`-hypothesis `H_j_arrives` are binders here as well.":
        "As in the Rocq original, every section variable declared before the theorem is abstracted, so the unused "
        "task parameters, `job_deadline` and the `arr_seq`-hypothesis `H_j_arrives` are binders here as well.",
    "Binder lists follow the Rocq contract (`num_cpus` is a `Context`, hence implicit).":
        "Binder lists follow the Rocq original (`num_cpus` is a `Context`, hence implicit).",
    "Binder lists follow the Rocq contract (the unused section variable `tsk_k` of `WorkloadBoundDef` is not "
    "abstracted by the definitions).":
        "Binder lists follow the Rocq original (the unused section variable `tsk_k` of `WorkloadBoundDef` is not "
        "abstracted by the definitions).",
    "Binder lists follow the Rocq contract.": "Binder lists follow the Rocq original.",
}

def strip_contract_sentences(doc):
    doc = doc.replace(" (classic-prosa representation addendum)", "")
    for a, b in BINDER_SENTENCES.items():
        doc = doc.replace(a, b)
    # drop sentences that refer to the translation pipeline
    parts = re.split(r"(?<=[.;])\s+", doc)
    keep = [p for p in parts if not re.search(r"contract|classic-prosa/|ProsaBuddy|`About`|Rocq 9", p)]
    return " ".join(keep)

def reflow(paragraph, width=100):
    words = paragraph.split()
    lines, cur = [], ""
    for w in words:
        if cur and len(cur) + 1 + len(w) > width:
            lines.append(cur); cur = w
        else:
            cur = (cur + " " + w) if cur else w
    if cur: lines.append(cur)
    return "\n".join(lines)

def clean_docblock(block):
    """block is the inside of a `/-! ... -/` comment; clean it paragraph by paragraph."""
    paras = [p.strip() for p in re.split(r"\n\s*\n", block) if p.strip()]
    out = []
    for p in paras:
        if p.startswith("*") or "\n*" in p:          # bullet list: clean each bullet
            items = re.split(r"\n(?=\* )", p)
            items = [strip_contract_sentences(" ".join(i.split())) for i in items]
            items = [i for i in items if i.strip("* ").strip()]
            if items: out.append("\n".join(reflow(i) for i in items))
        else:
            q = strip_contract_sentences(" ".join(p.split()))
            if q.strip(): out.append(reflow(q))
    return "\n\n".join(out)

# ---------------------------------------------------------------- case studies
def case_info(case, path):
    solved = (LEAN / "CaseStudies" / path).read_text()
    ns = re.search(r"^namespace (\S+)", solved, re.M).group(1)
    m = last_theorem(solved)
    name = m.group(1)
    sig_start = m.end()
    end_idx = solved.rindex(f"\nend {ns}")
    binders, concl, proof = split_signature(solved[sig_start:end_idx])
    proof_file = HERE / "proofs" / f"{case}.lean"
    helpers, proof_imports = "", []
    if proof_file.exists():
        h, _, _ = proof_file.read_text().partition("-- @@PROOF@@\n")
        proof_imports = [l for l in h.splitlines() if l.startswith("import ")]
        helpers = "\n".join(l for l in h.splitlines() if not l.startswith("import ")).strip()
    return dict(solved=solved, ns=ns, name=name, theorem_start=m.start(), end_idx=end_idx,
                binders=binders, concl=concl, proof=proof, helpers=helpers, proof_imports=proof_imports)

def universes_of(text):
    us = []
    for u in ("u", "v"):
        if re.search(rf"\bType {u}\b", text): us.append(u)
    return us

def frozen_module(case, path, info):
    s = info["solved"]
    pre = s[:info["theorem_start"]]
    if info["helpers"]:
        assert info["helpers"] in pre, case
        pre = pre.replace(info["helpers"], "")
    lines = pre.split("\n")
    while lines and lines[0].startswith("--"):      # old header comment
        lines.pop(0)
    out = []
    skip_cont = False
    for l in lines:
        if skip_cont:
            skip_cont = l.startswith("  ");
            if skip_cont: continue
        if l.startswith("import CaseStudies.") or l in PROOF_ONLY_IMPORTS or l in info["proof_imports"]:
            continue
        if l.startswith("open CaseStudies."):
            skip_cont = True; continue
        out.append(l)
    pre = "\n".join(out)
    if case == "2005-ECRTS-Theorem6":
        pre = pre.replace("open Prosa.Util.Sum (sumFiltered sumSeq)", "open Prosa.Util.Sum (sumFiltered)")
    pre = re.sub(r"/-!\n(.*?)\n-/", lambda m: "/-!\n" + clean_docblock(m.group(1)) + "\n-/", pre, count=1, flags=re.S)
    pre = re.sub(r"\n{3,}", "\n\n", pre).rstrip() + "\n\n"
    rocq = status.MAN[case]["file"]
    paper = status.PAPERS["-".join(case.split("-")[:2])]
    header = (f"-- Case study {case}: {paper}.\n"
              f"-- Original Rocq statement: RTS_Papers/{rocq}.\n"
              f"-- Benchmark file: read-only.  Prove `{info['ns']}.{info['name']}_statement` in `Solution.lean` "
              f"(this folder).\n")
    name = info["name"]
    stmt = (f"/-- The statement of the case study's theorem `{name}`. -/\n"
            f"def {name}_statement : Prop :=\n"
            f"  ∀ {info['binders'].strip()},\n"
            f"    {info['concl'].strip()}\n")
    return header + pre.lstrip("\n") + stmt + f"\nend {info['ns']}\n"

def opens_of(text):
    return [l for l in text.splitlines() if l.startswith("open ") and not l.startswith("open CaseStudies.")]

def task_dir(path): return path[:-5]                                  # RTSS2007/Theorem1
def sol_ns(path): return "CaseStudies." + task_dir(path).replace("/", ".")
def stmt_mod(path): return sol_ns(path) + ".Statement"
def sol_mod(path): return sol_ns(path) + ".Solution"

def template(case, path, info, frozen_text):
    us = universes_of(frozen_text)
    uni = ".{" + ", ".join(us) + "}" if us else ""
    opens = "\n".join(opens_of(frozen_text))
    hint = (f"\nThe paper's statement and proof sketch (LaTeX) are in `proof.tex` in this folder.\n"
            if (PAPERS_DIR / case / HINT).exists() else "")
    return f"""import {stmt_mod(path)}

/-!
Benchmark task `{case}`: prove `{info['ns']}.{info['name']}_statement`
(defined in `Statement.lean` in this folder, which also contains the case study's definitions).
{hint}
Replace `sorry` with a proof.  You may add `import`s of modules of this package (`Prosa.*`, `Mathlib.*`),
helper definitions and lemmas, and new `.lean` files under `CaseStudies/` (for example next to this file).
Do not edit `Statement.lean`, `proof.tex` or anything outside `CaseStudies/`, and keep the name and type of
`solution`.  Check with `python3 benchmark/check.py {case}`.
-/

set_option linter.unusedVariables false

namespace {sol_ns(path)}

open {info['ns']}
{opens}

universe {' '.join(us)}

theorem solution : {info['name']}_statement{uni} := by
  sorry

end {sol_ns(path)}
"""

def rewrite_support(text):
    text = SUPPORT_RE.sub(lambda m: "CaseStudies.Support." + m.group(1), text)
    return text

def reference_solution(case, path, info, frozen_text):
    us = universes_of(frozen_text)
    uni = ".{" + ", ".join(us) + "}" if us else ""
    s = info["solved"]
    imports = [l for l in s.splitlines() if l.startswith("import ")]
    extra = [l for l in imports if l.startswith("import CaseStudies.") or l in PROOF_ONLY_IMPORTS]
    extra += info["proof_imports"]
    extra = [rewrite_support(l) for l in extra]
    extra = list(dict.fromkeys(["import CaseStudies.Support.Common"] + extra))
    opens = "\n".join(rewrite_support(l) for l in s.splitlines() if l.startswith("open "))
    # keep continuation lines of multi-line opens (2005-ECRTS-Theorem6)
    opens = "\n".join(rewrite_support(m.group(0)) for m in re.finditer(r"^open .*(?:\n  .*)*", s, re.M))
    helpers = rewrite_support(info["helpers"])
    thm = rewrite_support(s[info["theorem_start"]:info["end_idx"]].rstrip())
    body = (helpers + "\n\n" if helpers else "") + thm
    return (f"import {stmt_mod(path)}\n" + "\n".join(extra) + f"""

/-! Reference solution of benchmark task `{case}`. -/

set_option linter.unusedVariables false

universe {' '.join(us)}

namespace {info['ns']}

{opens}

{body}

end {info['ns']}

theorem {sol_ns(path)}.solution : {info['ns']}.{info['name']}_statement{uni} :=
  @{info['ns']}.{info['name']}
""")

def support_module(name):
    text = (LEAN / "CaseStudies" / f"{name}.lean").read_text()
    text = re.sub(r"^import CaseStudies\.(\w+)", lambda m: f"import CaseStudies.Support.{m.group(1)}", text, flags=re.M)
    return rewrite_support(text)

# ---------------------------------------------------------------- main
def main():
    out, ref, old = map(Path, sys.argv[1:4])
    if out.exists(): raise SystemExit(f"{out} exists")
    out.mkdir(parents=True)
    lib = accepted_library_files()
    for rel in lib:
        dst = out / rel; dst.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(WS / rel, dst)
    for f in ["LICENSE", "lean-toolchain", "lake-manifest.json", ".gitignore"]:
        shutil.copy2(old / f, out / f)
    shutil.copytree(old / "Examples", out / "Examples", ignore=shutil.ignore_patterns(".DS_Store"))
    tasks = []
    (ref / "CaseStudies" / "Support").mkdir(parents=True, exist_ok=True)
    for n in SUPPORT:
        (ref / "CaseStudies" / "Support" / f"{n}.lean").write_text(support_module(n))
    for case, path in status.PATHS.items():
        info = case_info(case, path)
        fz = frozen_module(case, path, info)
        d = task_dir(path)
        for p, text in [(out / "CaseStudies" / d / "Statement.lean", fz),
                        (out / "CaseStudies" / d / "Solution.lean", template(case, path, info, fz)),
                        (ref / "CaseStudies" / d / "Solution.lean", reference_solution(case, path, info, fz))]:
            p.parent.mkdir(parents=True, exist_ok=True); p.write_text(text)
        hint = PAPERS_DIR / case / HINT
        if hint.exists():
            shutil.copy2(hint, out / "CaseStudies" / d / HINT)
        group = "-".join(case.split("-")[:2])
        tasks.append(dict(
            id=case, paper=status.PAPERS[group], rocq_original=f"RTS_Papers/{status.MAN[case]['file']}",
            folder=f"CaseStudies/{d}/",
            statement_module=stmt_mod(path), statement_file=f"CaseStudies/{d}/Statement.lean",
            statement=f"{info['ns']}.{info['name']}_statement", universes=universes_of(fz),
            solution_module=sol_mod(path), solution_file=f"CaseStudies/{d}/Solution.lean",
            solution=f"{sol_ns(path)}.solution",
            hint_file=f"CaseStudies/{d}/{HINT}" if hint.exists() else None,
            note=NOTE_OVERRIDES.get(case, status.NOTES.get(case, {}).get("note", ""))))
    (out / "CaseStudies.lean").write_text(
        "\n".join(f"import {t['statement_module']}" for t in tasks) +
        f"\n\n/-! The {len(tasks)} case-study statements (benchmark tasks); see `benchmark/README.md`. -/\n")
    (out / "benchmark").mkdir()
    (out / "benchmark" / "tasks.json").write_text(json.dumps(tasks, indent=2, ensure_ascii=False) + "\n")
    assets = HERE / "deliverable_assets"
    shutil.copy2(assets / "README.md", out / "README.md")
    shutil.copy2(assets / "lakefile.lean", out / "lakefile.lean")
    for f in ["check.py", "README.md", "PROMPT.md"]:
        shutil.copy2(assets / "benchmark" / f, out / "benchmark" / f)
    shutil.copy2(assets / "reference" / "README.md", ref / "README.md")
    write_frozen(out)
    print(f"library files {len(lib)}; tasks {len(tasks)}")
    # ProsaBuddy's Prosa-theorem benchmark (benchmark/prosa-theorems/), built from the exported library files
    subprocess.run([sys.executable, str(HERE / "theorem_benchmark.py"), str(out)], check=True)

def write_frozen(out):
    """sha256 of every file a benchmark solution must not change: the library, the examples, each task's
    `Statement.lean` and `proof.tex`, and the package configuration.  No file may be added under `Prosa/`."""
    files = {}
    for tree in ["Prosa", "Examples"]:
        for p in sorted((out / tree).rglob("*")):
            if p.is_file() and p.name != ".DS_Store":
                files[p.relative_to(out).as_posix()] = sha(p)
    for p in sorted((out / "CaseStudies").rglob("*")):
        if p.is_file() and p.name in ("Statement.lean", HINT):
            files[p.relative_to(out).as_posix()] = sha(p)
    for f in ["CaseStudies.lean", "lakefile.lean", "lean-toolchain", "lake-manifest.json",
              "benchmark/check.py", "benchmark/tasks.json"]:
        files[f] = sha(out / f)
    (out / "benchmark" / "frozen_sha256.json").write_text(json.dumps(
        {"closed_trees": ["Prosa"], "files": dict(sorted(files.items()))}, indent=1) + "\n")

if __name__ == "__main__":
    if sys.argv[1] == "--frozen-only":
        write_frozen(Path(sys.argv[2]))
    else:
        main()
