import CaseStudies.RTSS2009.Lemma4

/-!
Benchmark task `2009-RTSS-Lemma4`: prove `CaseStudies.RTSS2009.Lemma4.ResponseTimeAnalysisFP.Lemma4_09_statement`
(defined in `CaseStudies/RTSS2009/Lemma4.lean`, which also contains the case study's definitions).

Replace `sorry` with a proof.  You may add `import`s of modules of this package (`Prosa.*`, `Mathlib.*`,
your own `Solutions.*` modules), helper definitions and lemmas, and new files under `Solutions/`.  Do not edit
anything outside `Solutions/`, and keep the name and type of `solution`.  Check with
`python3 benchmark/check.py 2009-RTSS-Lemma4`.
-/

set_option linter.unusedVariables false

namespace Solutions.RTSS2009.Lemma4

open CaseStudies.RTSS2009.Lemma4.ResponseTimeAnalysisFP
open Prosa.Classic.Model.Time.Time
open Prosa.Classic.Model.Arrival.Basic.ArrivalSequence.ArrivalSequence
open Prosa.Classic.Model.Arrival.Basic.Task.SporadicTaskset
open Prosa.Classic.Model.Arrival.Basic.Job.Job
open Prosa.Classic.Model.Arrival.Basic.TaskArrival.TaskArrival
open Prosa.Classic.Model.Priority.Priority
open Prosa.Classic.Model.Schedule.Global.Basic.Schedule.Schedule
open Prosa.Classic.Model.Schedule.Global.Basic.Schedule.ScheduleOfSporadicTask
open Prosa.Classic.Model.Schedule.Global.Workload.Workload
open Prosa.Classic.Model.Schedule.Global.Schedulability.Schedulability
open Prosa.Classic.Model.Schedule.Global.ResponseTime.ResponseTime
open Prosa.Classic.Model.Schedule.Global.Basic.Platform.Platform
open Prosa.Classic.Model.Schedule.Global.Basic.Interference.Interference
open Prosa.Classic.Util.DivMod (div_floor div_ceil)
open Prosa.Util.Sum (sumSeq sumFiltered)

universe u v

theorem solution : Lemma4_09_statement.{u, v} := by
  sorry

end Solutions.RTSS2009.Lemma4
