import CaseStudies.RTSS2007.Theorem2

/-!
Benchmark task `2007-RTSS-Theorem2`: prove `CaseStudies.RTSS2007.Theorem2.ResponseTimeAnalysisFP.theorem_2_statement`
(defined in `CaseStudies/RTSS2007/Theorem2.lean`, which also contains the case study's definitions).

Replace `sorry` with a proof.  You may add `import`s of modules of this package (`Prosa.*`, `Mathlib.*`,
your own `Solutions.*` modules), helper definitions and lemmas, and new files under `Solutions/`.  Do not edit
anything outside `Solutions/`, and keep the name and type of `solution`.  Check with
`python3 benchmark/check.py 2007-RTSS-Theorem2`.
-/

set_option linter.unusedVariables false

namespace Solutions.RTSS2007.Theorem2

open CaseStudies.RTSS2007.Theorem2.ResponseTimeAnalysisFP
open Prosa.Classic.Model.Time.Time
open Prosa.Classic.Model.Arrival.Basic.ArrivalSequence.ArrivalSequence
open Prosa.Classic.Model.Schedule.Global.Basic.Schedule.Schedule
open Prosa.Classic.Model.Schedule.Global.Workload.Workload
open Prosa.Classic.Model.Schedule.Global.Basic.Interference.Interference

universe u v

theorem solution : theorem_2_statement.{u, v} := by
  sorry

end Solutions.RTSS2007.Theorem2
