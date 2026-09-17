-- Translated from: ../rt-proofs/classic/model/schedule/uni/schedule_of_task.v
import Prosa.Classic.Model.Time
import Prosa.Classic.Model.Schedule.Uni.Schedule
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals

namespace Prosa.Classic.Model.Schedule.Uni.Schedule_of_task

open Prosa.Classic.Model.Time
open Prosa.Classic.Model.Schedule.Uni.Schedule

section ScheduleProperties

variable {Task : Type _} [DecidableEq Task]
variable {Job : Type _} [DecidableEq Job]
variable (job_cost : Job → Time)
variable (job_task : Job → Task)
variable (sched : schedule Job)

section TaskProperties

variable (tsk : Task)

def task_scheduled_at (t : Time) : Bool :=
  match sched t with
  | some j => job_task j == tsk
  | none => false

def task_service_at (t : Time) : Nat :=
  (task_scheduled_at job_task sched tsk t).toNat

def task_service_during (t1 t2 : Time) : Nat :=
  ∑ t ∈ Finset.Ico t1 t2, task_service_at job_task sched tsk t

def task_service (t2 : Time) : Nat :=
  task_service_during job_task sched tsk 0 t2

end TaskProperties

end ScheduleProperties

end Prosa.Classic.Model.Schedule.Uni.Schedule_of_task
