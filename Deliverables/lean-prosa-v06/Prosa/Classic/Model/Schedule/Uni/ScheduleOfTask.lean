-- Authoritative source:
-- ProsaBuddy classic Prosa (prosabuddy commit f692cb7479780cf6009493f373a309e13165201c)
-- source: classic/model/schedule/uni/schedule_of_task.v
-- sha256: see Prosa-Shunqi/classic-prosa/comprehensive-classic/file_order.csv (rank 58)

import Prosa.Classic.Util.All
import Prosa.Classic.Model.Time
import Prosa.Classic.Model.Arrival.Basic.Task
import Prosa.Classic.Model.Arrival.Basic.Job
import Prosa.Classic.Model.Arrival.Basic.ArrivalSequence
import Prosa.Classic.Model.Schedule.Uni.Schedule

/-!
Uniprocessor schedules of tasks (Rocq module `ScheduleOfTask`, which `Export`s `SporadicTaskset` and
`UniprocessorSchedule`).

Representation notes: `if sched t is Some j then job_task j == tsk else false` is a match returning
`decide (job_task j = tsk)`; the Boolean-to-`nat` coercion is `Bool.toNat`; `\sum_(a <= t < b) F t` is
`∑ t ∈ Finset.Ico a b, F t`. Binder lists follow the Rocq contract (the unused `job_cost` is not abstracted).
-/

namespace Prosa.Classic.Model.Schedule.Uni.ScheduleOfTask.ScheduleOfTask

open Prosa.Classic.Model.Time.Time
open Prosa.Classic.Model.Schedule.Uni.Schedule.UniprocessorSchedule

universe u v

def task_scheduled_at {Task : Type u} [DecidableEq Task] {Job : Type v} [DecidableEq Job]
    (job_task : Job → Task) (sched : schedule Job) (tsk : Task) (t : time) : Bool :=
  match sched t with
  | some j => decide (job_task j = tsk)
  | none => false

def task_service_at {Task : Type u} [DecidableEq Task] {Job : Type v} [DecidableEq Job]
    (job_task : Job → Task) (sched : schedule Job) (tsk : Task) (t : time) : time :=
  (task_scheduled_at job_task sched tsk t).toNat

def task_service_during {Task : Type u} [DecidableEq Task] {Job : Type v} [DecidableEq Job]
    (job_task : Job → Task) (sched : schedule Job) (tsk : Task) (t1 t2 : time) : Nat :=
  ∑ t ∈ Finset.Ico t1 t2, task_service_at job_task sched tsk t

def task_service {Task : Type u} [DecidableEq Task] {Job : Type v} [DecidableEq Job]
    (job_task : Job → Task) (sched : schedule Job) (tsk : Task) (t2 : time) : Nat :=
  task_service_during job_task sched tsk 0 t2

end Prosa.Classic.Model.Schedule.Uni.ScheduleOfTask.ScheduleOfTask
