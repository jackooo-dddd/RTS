import CaseStudies.RTSS2007.Theorem4

/-!
Benchmark task `2007-RTSS-Theorem4`: prove `CaseStudies.RTSS2007.Theorem4.WorkloadBound.Theorem4_07_statement`
(defined in `CaseStudies/RTSS2007/Theorem4.lean`, which also contains the case study's definitions).

Replace `sorry` with a proof.  You may add `import`s of modules of this package (`Prosa.*`, `Mathlib.*`,
your own `Solutions.*` modules), helper definitions and lemmas, and new files under `Solutions/`.  Do not edit
anything outside `Solutions/`, and keep the name and type of `solution`.  Check with
`python3 benchmark/check.py 2007-RTSS-Theorem4`.
-/

set_option linter.unusedVariables false

namespace Solutions.RTSS2007.Theorem4

open CaseStudies.RTSS2007.Theorem4.WorkloadBound
open Prosa.Classic.Model.Time.Time
open Prosa.Classic.Model.Arrival.Basic.ArrivalSequence.ArrivalSequence
open Prosa.Classic.Model.Arrival.Basic.Task.SporadicTaskset
open Prosa.Classic.Model.Arrival.Basic.Job.Job
open Prosa.Classic.Model.Arrival.Basic.TaskArrival.TaskArrival
open Prosa.Classic.Model.Schedule.Global.Basic.Schedule.Schedule
open Prosa.Classic.Model.Schedule.Global.Workload.Workload
open Prosa.Classic.Model.Schedule.Global.Schedulability.Schedulability
open Prosa.Classic.Model.Schedule.Global.Basic.Platform.Platform
open Prosa.Classic.Util.DivMod (div_floor)

universe u v

theorem solution : Theorem4_07_statement.{u, v} := by
  sorry

end Solutions.RTSS2007.Theorem4
