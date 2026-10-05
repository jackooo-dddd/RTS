-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/definitions/workload/elf_athep_bound.v

import Prosa.Analysis.Definitions.RequestBoundFunction
import Prosa.Model.Priority.Elf
import Prosa.Util.Epsilon

namespace Prosa.Analysis.Definitions.Workload.ElfAthepBound

open Prosa.Behavior.Time
open Prosa.Model.Task.Concept
open Prosa.Model.Task.Arrival.Curves
open Prosa.Model.Priority.Definitions
open Prosa.Model.Priority.Gel
open Prosa.Analysis.Definitions.RequestBoundFunction
open Prosa.Util.Sum

/-! Representation notes: `\sum_(x <- xs | P x) F x` is the accepted
`sumFiltered xs P F`; `a != b` is `decide (a ≠ b)`; `minn` is `min`; `ε` is
`1`; as in the accepted `model/priority/gel.v`, `n%:R` on `int` is the cast
`(n : Int)`; `Num.max 0 x` is `max 0 x` and `` `|x| `` (`absz`) is
`Int.natAbs`; the local `let rbf_duration` is inlined. Binder orders follow
the elaborated types. -/

section ELFWorkloadBound

/-- The length of the interval in which a higher-or-equal-priority job of an
equal-priority task `tsk_o` can arrive and interfere with a job of `tsk`
arriving at relative offset `A`. -/
def ep_task_interfering_interval_length {Task : TaskType} [DecidableEq Task] [PriorityPoint Task]
    (tsk tsk_o : Task) (A : duration) : Int :=
  ((A + ε : Nat) : Int) + task_priority_point tsk - task_priority_point tsk_o

/-- Bound on the workload of higher-or-equal-priority jobs of the other
equal-priority tasks. -/
def bound_on_ep_task_workload {Task : TaskType} [DecidableEq Task] [TaskCost Task] [MaxArrivals Task]
    [PriorityPoint Task] (ts : List Task) [FP : FP_policy Task] (tsk : Task) (A delta : duration) : Nat :=
  sumFiltered ts (fun tsk_o => ep_task (FP := FP) tsk tsk_o && decide (tsk_o ≠ tsk))
    (fun tsk_o => task_request_bound_function tsk_o
      (min (Int.natAbs (max 0 (ep_task_interfering_interval_length tsk tsk_o A))) delta))

/-- Bound on the workload of the strictly higher-priority tasks. -/
def bound_on_hp_task_workload {Task : TaskType} [DecidableEq Task] [TaskCost Task] [MaxArrivals Task]
    (ts : List Task) [FP : FP_policy Task] (tsk : Task) (delta : duration) : Nat :=
  total_hp_request_bound_function_FP ts (FP := FP) tsk delta

/-- Bound on the workload of higher-or-equal-priority jobs of other tasks
under ELF. -/
def bound_on_athep_workload {Task : TaskType} [DecidableEq Task] [TaskCost Task] [MaxArrivals Task]
    [PriorityPoint Task] (ts : List Task) [FP : FP_policy Task] (tsk : Task) (A delta : duration) : Nat :=
  bound_on_hp_task_workload ts (FP := FP) tsk delta + bound_on_ep_task_workload ts (FP := FP) tsk A delta

end ELFWorkloadBound

end Prosa.Analysis.Definitions.Workload.ElfAthepBound
