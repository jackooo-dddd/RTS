import CaseStudies.RTCSA2014.Theorem3

/-!
Benchmark task `2014-RTCSA-Theorem3`: prove `CaseStudies.RTCSA2014.Theorem3.ResponseTimeAnalysisFP.Theorem3_14_statement`
(defined in `CaseStudies/RTCSA2014/Theorem3.lean`, which also contains the case study's definitions).

Replace `sorry` with a proof.  You may add `import`s of modules of this package (`Prosa.*`, `Mathlib.*`,
your own `Solutions.*` modules), helper definitions and lemmas, and new files under `Solutions/`.  Do not edit
anything outside `Solutions/`, and keep the name and type of `solution`.  Check with
`python3 benchmark/check.py 2014-RTCSA-Theorem3`.
-/

set_option linter.unusedVariables false

namespace Solutions.RTCSA2014.Theorem3

open CaseStudies.RTCSA2014.Theorem3.ResponseTimeAnalysisFP
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

theorem solution : Theorem3_14_statement.{u, v} := by
  sorry

end Solutions.RTCSA2014.Theorem3
