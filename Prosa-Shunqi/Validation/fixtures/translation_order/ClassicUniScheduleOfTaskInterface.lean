import Prosa.Classic.Model.Schedule.Uni.ScheduleOfTask

/-!
Validation-only interface for `classic/model/schedule/uni/schedule_of_task.v` (classic family): kernel-checked Lean
equations, exported with their proofs and used by the Rocq certificate as propositional equations
(transport) only.
-/

namespace Prosa.Validation.ClassicUniScheduleOfTaskInterface

open Lean Elab Command Meta
open Prosa.Classic.Model.Time.Time
open Prosa.Classic.Model.Schedule.Uni.Schedule.UniprocessorSchedule
open Prosa.Classic.Model.Schedule.Uni.ScheduleOfTask.ScheduleOfTask

universe u v

def task_service_during_proj {Task : Type u} [DecidableEq Task] {Job : Type v} [DecidableEq Job]
    (job_task : Job → Task) (sched : schedule Job) (tsk : Task) (t1 t2 : time) : Nat :=
  List.foldr Nat.add Nat.zero
    (List.map (fun t => task_service_at job_task sched tsk t) (List.range' t1 (Nat.sub t2 t1) (Nat.succ Nat.zero)))

theorem task_service_during_proj_guard : @task_service_during = @task_service_during_proj := rfl

end Prosa.Validation.ClassicUniScheduleOfTaskInterface
