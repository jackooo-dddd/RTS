import CaseStudies.ECRTS2005.Theorem6

/-!
Benchmark task `2005-ECRTS-Theorem6`: prove `CaseStudies.ECRTS2005.Theorem6.SchedulabilityAnalysisEDF.Theorem6_05_statement`
(defined in `CaseStudies/ECRTS2005/Theorem6.lean`, which also contains the case study's definitions).

Replace `sorry` with a proof.  You may add `import`s of modules of this package (`Prosa.*`, `Mathlib.*`,
your own `Solutions.*` modules), helper definitions and lemmas, and new files under `Solutions/`.  Do not edit
anything outside `Solutions/`, and keep the name and type of `solution`.  Check with
`python3 benchmark/check.py 2005-ECRTS-Theorem6`.
-/

set_option linter.unusedVariables false

namespace Solutions.ECRTS2005.Theorem6

open CaseStudies.ECRTS2005.Theorem6.SchedulabilityAnalysisEDF
open Prosa.Classic.Model.Time.Time
open Prosa.Classic.Model.Arrival.Basic.ArrivalSequence.ArrivalSequence
open Prosa.Classic.Model.Arrival.Basic.Task.SporadicTaskset
open Prosa.Classic.Model.Arrival.Basic.Job.Job
open Prosa.Classic.Model.Arrival.Basic.TaskArrival.TaskArrival
open Prosa.Classic.Model.Priority.Priority
open Prosa.Classic.Model.Schedule.Global.Basic.Schedule.Schedule
open Prosa.Classic.Model.Schedule.Global.Schedulability.Schedulability
open Prosa.Classic.Model.Schedule.Global.Basic.Platform.Platform
open Prosa.Classic.Model.Schedule.Global.Basic.Interference.Interference
open Prosa.Util.Sum (sumFiltered)

universe u v

theorem solution : Theorem6_05_statement.{u, v} := by
  sorry

end Solutions.ECRTS2005.Theorem6
