-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/definitions/request_bound_function.v

import Prosa.Util.Sum
import Prosa.Model.Task.Arrival.Curves
import Prosa.Model.Priority.Classes

namespace Prosa.Analysis.Definitions.RequestBoundFunction

open Prosa.Behavior.Time
open Prosa.Model.Task.Concept
open Prosa.Model.Task.Arrival.Curves
open Prosa.Model.Priority.Definitions
open Prosa.Util.Sum

/-! Representation notes: `\sum_(x <- xs) F x` is the accepted `sumSeq xs F`
and `\sum_(x <- xs | P x) F x` is the accepted `sumFiltered xs P F`;
`a != b` is `decide (a ≠ b)`. Binder orders follow the elaborated types. -/

section TaskWorkloadBoundedByArrivalCurves

variable {Task : TaskType} [DecidableEq Task] [TaskCost Task] [MaxArrivals Task]

/-- The request-bound function of a task: cost times maximum arrivals. -/
def task_request_bound_function (tsk : Task) (Δ : duration) : Nat :=
  task_cost tsk * max_arrivals tsk Δ

variable (ts : List Task)

/-- The total request-bound function of a task set. -/
def total_request_bound_function (Δ : duration) : Nat :=
  sumSeq ts (fun tsk => task_request_bound_function tsk Δ)

variable [FP : FP_policy Task]

/-- Total RBF of the tasks with higher-or-equal priority than `tsk`. -/
def total_hep_request_bound_function_FP (tsk : Task) (Δ : duration) : Nat :=
  sumFiltered ts (fun tsk_other => FP.hep_task tsk_other tsk)
    (fun tsk_other => task_request_bound_function tsk_other Δ)

/-- Total RBF of the other tasks with higher-or-equal priority than `tsk`. -/
def total_ohep_request_bound_function_FP (tsk : Task) (Δ : duration) : Nat :=
  sumFiltered ts (fun tsk_other => FP.hep_task tsk_other tsk && decide (tsk_other ≠ tsk))
    (fun tsk_other => task_request_bound_function tsk_other Δ)

/-- Total RBF of the tasks with equal priority to `tsk`. -/
def total_ep_request_bound_function_FP (tsk : Task) (Δ : duration) : Nat :=
  sumFiltered ts (fun tsk_other => ep_task (FP := FP) tsk_other tsk)
    (fun tsk_other => task_request_bound_function tsk_other Δ)

/-- Total RBF of the tasks with strictly higher priority than `tsk`. -/
def total_hp_request_bound_function_FP (tsk : Task) (Δ : duration) : Nat :=
  sumFiltered ts (fun tsk_other => hp_task (FP := FP) tsk_other tsk)
    (fun tsk_other => task_request_bound_function tsk_other Δ)

end TaskWorkloadBoundedByArrivalCurves

end Prosa.Analysis.Definitions.RequestBoundFunction
