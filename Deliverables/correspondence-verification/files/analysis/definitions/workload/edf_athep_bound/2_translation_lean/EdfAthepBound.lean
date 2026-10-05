-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/definitions/workload/edf_athep_bound.v

import Prosa.Analysis.Definitions.RequestBoundFunction
import Prosa.Util.Epsilon

namespace Prosa.Analysis.Definitions.Workload.EdfAthepBound

open Prosa.Behavior.Time
open Prosa.Model.Task.Concept
open Prosa.Model.Task.Arrival.Curves
open Prosa.Analysis.Definitions.RequestBoundFunction
open Prosa.Util.Sum

/-! Representation notes: `\sum_(x <- xs | P x) F x` is the accepted
`sumFiltered xs P F`; `a != b` is `decide (a ≠ b)`; `minn` is `min`; `ε` is
`1`; the section-local `Let D tsk := task_deadline tsk` and `Let rbf :=
task_request_bound_function` are inlined. Binder orders follow the elaborated
types. -/

section EDFWorkloadBound

variable {Task : TaskType} [DecidableEq Task] [TaskCost Task] [TaskDeadline Task] [MaxArrivals Task]

/-- Bound on the workload of higher-or-equal-priority jobs of other tasks
under EDF. -/
def bound_on_athep_workload (ts : List Task) (tsk : Task) (A Δ : Nat) : Nat :=
  sumFiltered ts (fun tsk_o => decide (tsk_o ≠ tsk))
    (fun tsk_o => task_request_bound_function tsk_o
      (min ((A + ε) + task_deadline tsk - task_deadline tsk_o) Δ))

end EDFWorkloadBound

end Prosa.Analysis.Definitions.Workload.EdfAthepBound
