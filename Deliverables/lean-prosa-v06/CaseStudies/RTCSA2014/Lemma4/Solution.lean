import CaseStudies.RTCSA2014.Lemma4.Statement

/-!
Benchmark task `2014-RTCSA-Lemma4`: prove `CaseStudies.RTCSA2014.Lemma4.ResponseTimeAnalysisFP.Lemma4_14_statement`
(defined in `Statement.lean` in this folder, which also contains the case study's definitions).

The paper's statement and proof sketch (LaTeX) are in `proof.tex` in this folder.

Replace `sorry` with a proof.  You may add `import`s of modules of this package (`Prosa.*`, `Mathlib.*`),
helper definitions and lemmas, and new `.lean` files under `CaseStudies/` (for example next to this file).
Do not edit `Statement.lean`, `proof.tex` or anything outside `CaseStudies/`, and keep the name and type of
`solution`.  Check with `python3 benchmark/check.py 2014-RTCSA-Lemma4`.
-/

set_option linter.unusedVariables false

namespace CaseStudies.RTCSA2014.Lemma4

open CaseStudies.RTCSA2014.Lemma4.ResponseTimeAnalysisFP
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

theorem solution : Lemma4_14_statement.{u, v} := by
  sorry

end CaseStudies.RTCSA2014.Lemma4
