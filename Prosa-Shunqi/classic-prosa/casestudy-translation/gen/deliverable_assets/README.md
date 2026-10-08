# lean-prosa-v06

A Lean 4 version of [Prosa](https://prosa.mpi-sws.org), a library of real-time scheduling theory: jobs,
schedules, service, busy intervals, and response-time analyses. The package contains:

- **Prosa v0.6**: all 357 source files (2439 declarations) of Prosa v0.6, under `Prosa/` (outside
  `Prosa/Classic`).
- **Classic Prosa**: all 190 source files of classic Prosa (models, utilities, implementations, and the
  uniprocessor, global, APA, jitter, self-suspension and sustainability analyses), under `Prosa/Classic/`.
- **A proof benchmark**: 24 case studies from real-time systems papers, stated in Lean over classic Prosa,
  with a checker for testing whether a model (or a person) can prove them. See
  [`benchmark/README.md`](benchmark/README.md).
- **A second benchmark, of Prosa's own theorems**: the 130 theorems (65 training, 65 test, levels 1–7) of
  ProsaBuddy's evaluation set. Each task removes one theorem's proof from its Lean file and asks for it again.
  See [`benchmark/prosa-theorems/README.md`](benchmark/prosa-theorems/README.md).

Only Lean is needed. You do not need Rocq/Coq, OCaml, or the original Prosa repository.

## Requirements

- [elan](https://github.com/leanprover/elan): installs the right Lean version (`v4.33.1`, from
  `lean-toolchain`) and Lake automatically.
- Git, curl, and Python 3 (for the benchmark checker only).
- Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`. Lake fetches it and every other dependency at the
  exact revisions pinned in `lake-manifest.json`. Don't run `lake update`, because it would change those
  revisions.

## Install and build

1. Install Git and curl.
   - Linux (Debian/Ubuntu): `sudo apt install git curl`
   - macOS: Git comes with the Xcode Command Line Tools or Homebrew.
   - Windows: use WSL2. In PowerShell, run `wsl --install -d Ubuntu`, then do everything inside Ubuntu.
     Keep the project under `~/`, not `/mnt/c`.

2. Install elan:
   ```sh
   curl https://elan.lean-lang.org/elan-init.sh -sSf | sh
   ```
   Then open a new terminal.

3. From this folder, run:
   ```sh
   lake exe cache get                      # download dependencies and prebuilt Mathlib
   lake build                              # build the library and the case-study statements
   lake env lean Examples/RTSExample.lean  # check the example
   ```

Tested on macOS (Apple silicon). Linux and WSL2 follow the same steps but have not been tested.

## Use it in your project

In your `lakefile.lean`:

```lean
require lean_prosa_v06 from git "<repository-url>" @ "<commit>"
-- or a local copy:
-- require lean_prosa_v06 from "path/to/lean-prosa-v06"
```

Use the same `lean-toolchain` (`leanprover/lean4:v4.33.1`). Import modules directly, for example:

```lean
import Prosa.Analysis.Facts.Behavior.Service
import Prosa.Classic.Analysis.Global.Basic.BertognaFpTheory
```

Modules mirror Prosa's file layout. For example, `analysis/facts/behavior/service.v` becomes
`Prosa.Analysis.Facts.Behavior.Service`, and classic Prosa's `classic/analysis/global/basic/bertogna_fp_theory.v`
becomes `Prosa.Classic.Analysis.Global.Basic.BertognaFpTheory`. Each file names its original `.v` source at
the top.

## Example

`Examples/RTSExample.lean` proves Prosa's `completion_monotonic` (from `analysis/facts/behavior/completion.v`):
once a job has completed, it stays completed. The proof builds on the library's definitions and the lemma
`service_cat`. It depends only on Lean's standard axioms (`propext`, `Classical.choice`, `Quot.sound`).

## What's included

- `Prosa/` (except `Prosa/Classic`): Prosa v0.6 (commit `414e66760333eaa4ef78c685bcf53291c527a548`), all 357
  source files and 2439 declarations. Every Lean statement was checked against the original Rocq
  statement, and every proof is complete (no `sorry`).
- `Prosa/Classic/`: classic Prosa as shipped with ProsaBuddy (commit `f692cb7`), all 190 files and 2033
  declarations, every proof complete. 178 files were checked the same way as Prosa v0.6. The 12
  `Prosa/Classic/Implementation/**/*Example.lean` files (96 declarations: concrete task sets and their
  analysis results) were checked more lightly: their Rocq originals compile, and every declaration is present
  in Lean with a complete proof, but their statements were not compared one by one with the Rocq ones.
- `CaseStudies/`: the case-study benchmark, one folder per task, `CaseStudies/<G>/<F>/`, containing the
  read-only statement `Statement.lean` (`<theorem>_statement : Prop` and the definitions it uses), the hint
  `proof.tex` (the paper's statement and proof sketch in LaTeX; 22 of the 24 tasks have one), and the
  workspace `Solution.lean`, which ends in `sorry`.
- `benchmark/`: the task list, the checker, and the instructions for running the case-study benchmark.
- `benchmark/prosa-theorems/`: ProsaBuddy's 130 Prosa theorems (task list, `prepare.py`, `check.py`,
  instructions, and ProsaBuddy's original table).

| Task | Folder | Statement to prove | Hint |
|---|---|---|---|
| `2005-ECRTS-Lemma3` | `CaseStudies/ECRTS2005/Lemma3/` | `CaseStudies.ECRTS2005.Lemma3.ResponseTimeAnalysisEDF.Lemma3_05_statement` | `proof.tex` |
| `2005-ECRTS-Lemma4` | `CaseStudies/ECRTS2005/Lemma4/` | `CaseStudies.ECRTS2005.Lemma4.ResponseTimeAnalysisEDF.Lemma4_05_statement` | `proof.tex` |
| `2005-ECRTS-Theorem6` | `CaseStudies/ECRTS2005/Theorem6/` | `CaseStudies.ECRTS2005.Theorem6.SchedulabilityAnalysisEDF.Theorem6_05_statement` | `proof.tex` |
| `2007-RTSS-Theorem1` | `CaseStudies/RTSS2007/Theorem1/` | `CaseStudies.RTSS2007.Theorem1.ResponseTimeAnalysisFP.Theorem1_07_statement` | `proof.tex` |
| `2007-RTSS-Theorem2` | `CaseStudies/RTSS2007/Theorem2/` | `CaseStudies.RTSS2007.Theorem2.ResponseTimeAnalysisFP.theorem_2_statement` | `proof.tex` |
| `2007-RTSS-Theorem3` | `CaseStudies/RTSS2007/Theorem3/` | `CaseStudies.RTSS2007.Theorem3.ResponseTimeAnalysisFP.Theorem3_07_statement` | `proof.tex` |
| `2007-RTSS-Theorem4` | `CaseStudies/RTSS2007/Theorem4/` | `CaseStudies.RTSS2007.Theorem4.WorkloadBound.Theorem4_07_statement` | `proof.tex` |
| `2009-RTSS-Extend1_10` | `CaseStudies/RTSS2009/Extend1_10/` | `CaseStudies.RTSS2009.Extend1_10.ResponseTimeAnalysisFP.Method1_10_09_statement` | — |
| `2009-RTSS-Lemma1` | `CaseStudies/RTSS2009/Lemma1/` | `CaseStudies.RTSS2009.Lemma1.ResponseTimeAnalysisFP.Lemma1_09_statement` | `proof.tex` |
| `2009-RTSS-Lemma1_2` | `CaseStudies/RTSS2009/Lemma1_2/` | `CaseStudies.RTSS2009.Lemma1_2.ResponseTimeAnalysisFP.Lemma1_09_statement` | `proof.tex` |
| `2009-RTSS-Lemma2-1` | `CaseStudies/RTSS2009/Lemma2_1/` | `CaseStudies.RTSS2009.Lemma2_1.ResponseTimeAnalysisFP.Lemma2_09_statement` | `proof.tex` |
| `2009-RTSS-Lemma2-2` | `CaseStudies/RTSS2009/Lemma2_2/` | `CaseStudies.RTSS2009.Lemma2_2.ResponseTimeAnalysisFP.Lemma2_09_statement` | `proof.tex` |
| `2009-RTSS-Lemma3` | `CaseStudies/RTSS2009/Lemma3/` | `CaseStudies.RTSS2009.Lemma3.ResponseTimeAnalysisFP.Lemma3_09_statement` | `proof.tex` |
| `2009-RTSS-Lemma4` | `CaseStudies/RTSS2009/Lemma4/` | `CaseStudies.RTSS2009.Lemma4.ResponseTimeAnalysisFP.Lemma4_09_statement` | `proof.tex` |
| `2009-RTSS-Lemma5` | `CaseStudies/RTSS2009/Lemma5/` | `CaseStudies.RTSS2009.Lemma5.ResponseTimeAnalysisFP.Lemma5_09_statement` | `proof.tex` |
| `2009-RTSS-Method1` | `CaseStudies/RTSS2009/Method1/` | `CaseStudies.RTSS2009.Method1.ResponseTimeAnalysisFP.gn_method1_statement` | — |
| `2009-RTSS-Theorem1` | `CaseStudies/RTSS2009/Theorem1/` | `CaseStudies.RTSS2009.Theorem1.ResponseTimeAnalysisFP.Theorem1_09_statement` | `proof.tex` |
| `2009-RTSS-Theorem2` | `CaseStudies/RTSS2009/Theorem2/` | `CaseStudies.RTSS2009.Theorem2.ResponseTimeAnalysisFP.Theorem2_statement` | `proof.tex` |
| `2014-RTCSA-Lemma4` | `CaseStudies/RTCSA2014/Lemma4/` | `CaseStudies.RTCSA2014.Lemma4.ResponseTimeAnalysisFP.Lemma4_14_statement` | `proof.tex` |
| `2014-RTCSA-Lemma5` | `CaseStudies/RTCSA2014/Lemma5/` | `CaseStudies.RTCSA2014.Lemma5.ResponseTimeAnalysisFP.Lemma5_14_statement` | `proof.tex` |
| `2014-RTCSA-Theorem3` | `CaseStudies/RTCSA2014/Theorem3/` | `CaseStudies.RTCSA2014.Theorem3.ResponseTimeAnalysisFP.Theorem3_14_statement` | `proof.tex` |
| `2015-BOOK-Lemma18.1` | `CaseStudies/BOOK2015/Lemma18_1/` | `CaseStudies.BOOK2015.Lemma18_1.ResponseTimeAnalysisFP.Lemma18_1_15_statement` | `proof.tex` |
| `2015-book-Theorem18_6` | `CaseStudies/BOOK2015/Theorem18_6/` | `CaseStudies.BOOK2015.Theorem18_6.Theorem18_6_statement` | `proof.tex` |
| `2015-RTAS-Lemma8` | `CaseStudies/RTAS2015/Lemma8/` | `CaseStudies.RTAS2015.Lemma8.ResponseTimeAnalysisFP.bertogna_cirinei_response_time_bound_fp_statement` | `proof.tex` |

## License

This is derived from Prosa, which is BSD 2-Clause licensed. See `LICENSE`.
