import CaseStudies.RTSS2007.Theorem2.Statement

/-!
Benchmark task `2007-RTSS-Theorem2`: prove `CaseStudies.RTSS2007.Theorem2.ResponseTimeAnalysisFP.theorem_2_statement`
(defined in `Statement.lean` in this folder, which also contains the case study's definitions).

The paper's statement and proof sketch (LaTeX) are in `proof.tex` in this folder.

Replace `sorry` with a proof.  You may add `import`s of modules of this package (`Prosa.*`, `Mathlib.*`),
helper definitions and lemmas, and new `.lean` files under `CaseStudies/` (for example next to this file).
Do not edit `Statement.lean`, `proof.tex` or anything outside `CaseStudies/`, and keep the name and type of
`solution`.  Check with `python3 benchmark/check.py 2007-RTSS-Theorem2`.
-/

set_option linter.unusedVariables false

namespace CaseStudies.RTSS2007.Theorem2

open CaseStudies.RTSS2007.Theorem2.ResponseTimeAnalysisFP
open Prosa.Classic.Model.Time.Time
open Prosa.Classic.Model.Arrival.Basic.ArrivalSequence.ArrivalSequence
open Prosa.Classic.Model.Schedule.Global.Basic.Schedule.Schedule
open Prosa.Classic.Model.Schedule.Global.Workload.Workload
open Prosa.Classic.Model.Schedule.Global.Basic.Interference.Interference

universe u v

theorem solution : theorem_2_statement.{u, v} := by
  sorry

end CaseStudies.RTSS2007.Theorem2
