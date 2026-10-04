import CaseStudies.RTAS2015.Lemma8

/-!
Benchmark task `2015-RTAS-Lemma8`: prove `CaseStudies.RTAS2015.Lemma8.ResponseTimeAnalysisFP.bertogna_cirinei_response_time_bound_fp_statement`
(defined in `CaseStudies/RTAS2015/Lemma8.lean`, which also contains the case study's definitions).

Replace `sorry` with a proof.  You may add `import`s of modules of this package (`Prosa.*`, `Mathlib.*`,
your own `Solutions.*` modules), helper definitions and lemmas, and new files under `Solutions/`.  Do not edit
anything outside `Solutions/`, and keep the name and type of `solution`.  Check with
`python3 benchmark/check.py 2015-RTAS-Lemma8`.
-/

set_option linter.unusedVariables false

namespace Solutions.RTAS2015.Lemma8

open CaseStudies.RTAS2015.Lemma8.ResponseTimeAnalysisFP
open Prosa.Classic.Model.Time.Time
open Prosa.Classic.Model.Arrival.Basic.ArrivalSequence.ArrivalSequence
open Prosa.Classic.Model.Arrival.Basic.Task.SporadicTaskset
open Prosa.Classic.Model.Arrival.Basic.Job.Job
open Prosa.Classic.Model.Arrival.Basic.TaskArrival.TaskArrival
open Prosa.Classic.Model.Priority.Priority
open Prosa.Classic.Model.Schedule.Global.Basic.Schedule.Schedule
open Prosa.Classic.Model.Schedule.Global.ResponseTime.ResponseTime
open Prosa.Classic.Model.Schedule.Apa.Affinity.Affinity
open Prosa.Classic.Model.Schedule.Apa.Interference.Interference
open Prosa.Classic.Model.Schedule.Apa.Platform.Platform
open Prosa.Classic.Util.DivMod (div_floor)
open Prosa.Util.Sum (sumFiltered)

universe u v

theorem solution : bertogna_cirinei_response_time_bound_fp_statement.{u, v} := by
  sorry

end Solutions.RTAS2015.Lemma8
