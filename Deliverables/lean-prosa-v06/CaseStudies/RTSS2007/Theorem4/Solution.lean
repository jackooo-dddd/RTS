import CaseStudies.RTSS2007.Theorem4.Statement

/-!
Benchmark task `2007-RTSS-Theorem4`: prove `CaseStudies.RTSS2007.Theorem4.WorkloadBound.Theorem4_07_statement`
(defined in `Statement.lean` in this folder, which also contains the case study's definitions).

The paper's statement and proof sketch (LaTeX) are in `proof.tex` in this folder.

Replace `sorry` with a proof.  You may add `import`s of modules of this package (`Prosa.*`, `Mathlib.*`),
helper definitions and lemmas, and new `.lean` files under `CaseStudies/` (for example next to this file).
Do not edit `Statement.lean`, `proof.tex` or anything outside `CaseStudies/`, and keep the name and type of
`solution`.  Check with `python3 benchmark/check.py 2007-RTSS-Theorem4`.
-/

set_option linter.unusedVariables false

namespace CaseStudies.RTSS2007.Theorem4

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

end CaseStudies.RTSS2007.Theorem4
