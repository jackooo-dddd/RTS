-- Authoritative source:
-- ProsaBuddy classic Prosa (prosabuddy commit f692cb7479780cf6009493f373a309e13165201c)
-- source: classic/model/schedule/partitioned/schedule.v
-- sha256: see Prosa-Shunqi/classic-prosa/comprehensive-classic/file_order.csv (rank 80)

import Prosa.Classic.Util.All
import Prosa.Classic.Model.Time
import Prosa.Classic.Model.Arrival.Basic.Task
import Prosa.Classic.Model.Arrival.Basic.Job
import Prosa.Classic.Model.Schedule.Global.Schedulability
import Prosa.Classic.Model.Schedule.Global.Basic.Schedule
import Prosa.Classic.Model.Schedule.Uni.Schedule
import Prosa.Classic.Model.Schedule.Uni.Schedulability

/-!
Partitioned schedules (Rocq module `Partitioned`).

Representation notes:
* The module aliases `uni` (`UniprocessorSchedule`) and `uni_sched` (`Schedulability` of the uniprocessor model)
  declare nothing; the corresponding Lean namespaces are used directly where needed. `Export Time` is not
  replicated (Lean has no re-export); `time` is the classic `Prosa.Classic.Model.Time.Time.time`.
* `scheduled_on sched j cpu t` is the accepted global Boolean `Schedule.scheduled_on`, used as `= true`;
  `tsk \in ts` is `tsk ∈ ts`.
* Binder lists follow the Rocq contract (`{Job} {num_cpus} sched j …`).
-/

set_option linter.unusedVariables false

namespace Prosa.Classic.Model.Schedule.Partitioned.Schedule.Partitioned

open Prosa.Classic.Model.Time.Time
open Prosa.Classic.Model.Schedule.Global.Basic.Schedule.Schedule

universe u v

def never_migrates {Job : Type v} [DecidableEq Job] {num_cpus : Nat} (sched : schedule Job num_cpus) (j : Job) :
    Prop :=
  ∀ t, ∀ cpu, scheduled_on sched j cpu t = true →
    ∀ t', ∀ cpu', scheduled_on sched j cpu' t' = true → cpu' = cpu

def job_local_to_processor {Job : Type v} [DecidableEq Job] {num_cpus : Nat} (sched : schedule Job num_cpus)
    (j : Job) (assigned_cpu : processor num_cpus) : Prop :=
  ∀ t, ∀ cpu, scheduled_on sched j cpu t = true → cpu = assigned_cpu

def task_local_to_processor {Task : Type u} [DecidableEq Task] {Job : Type v} [DecidableEq Job]
    (job_task : Job → Task) {num_cpus : Nat} (sched : schedule Job num_cpus) (tsk : Task)
    (assigned_cpu : processor num_cpus) : Prop :=
  ∀ j, job_task j = tsk → job_local_to_processor sched j assigned_cpu

def partitioned_schedule {Task : Type u} [DecidableEq Task] {Job : Type v} [DecidableEq Job]
    (job_task : Job → Task) {num_cpus : Nat} (sched : schedule Job num_cpus) (ts : List Task)
    (assigned_cpu : Task → processor num_cpus) : Prop :=
  ∀ tsk, tsk ∈ ts → task_local_to_processor job_task sched tsk (assigned_cpu tsk)

theorem local_jobs_dont_migrate {Job : Type v} [DecidableEq Job] {num_cpus : Nat} (sched : schedule Job num_cpus)
    (j : Job) :
    ∀ cpu, job_local_to_processor sched j cpu → never_migrates sched j := by
  intro cpu H_is_local t cpu' H_sched_at_t t' cpu'' H_sched_at_t'
  rw [H_is_local t cpu' H_sched_at_t, H_is_local t' cpu'' H_sched_at_t']

end Prosa.Classic.Model.Schedule.Partitioned.Schedule.Partitioned
