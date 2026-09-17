-- Translated from: ../rt-proofs/classic/model/schedule/partitioned/schedule.v
import Prosa.Classic.Util.All
import Prosa.Classic.Model.Time
import Prosa.Classic.Model.Schedule.Global.Schedulability
import Prosa.Classic.Model.Schedule.Global.Basic.Schedule
import Prosa.Classic.Model.Schedule.Uni.Schedule
import Mathlib.Tactic

namespace Prosa.Classic.Model.Schedule.Partitioned.Schedule

open Prosa.Classic.Model.Time
open Prosa.Classic.Model.Arrival.Basic.Arrival_sequence
open Prosa.Classic.Model.Schedule.Global.Basic.Schedule
open Schedule

namespace Partitioned

section PartitionedDefs

variable {Task : Type _} [DecidableEq Task]
variable {Job : Type _} [DecidableEq Job]
variable (job_task : Job → Task)
variable (arr_seq : arrival_sequence Job)
variable {num_cpus : ℕ}
variable (sched : schedule Job num_cpus)

section NoJobMigration

variable (j : Job)

def never_migrates : Prop :=
  ∀ t, ∀ cpu : processor num_cpus,
    scheduled_on sched j cpu t = true →
    ∀ t', ∀ cpu' : processor num_cpus,
      scheduled_on sched j cpu' t' = true → cpu' = cpu

variable (assigned_cpu : processor num_cpus)

def job_local_to_processor : Prop :=
  ∀ t, ∀ cpu : processor num_cpus,
    scheduled_on sched j cpu t = true → cpu = assigned_cpu

end NoJobMigration

section NoTaskMigration

variable (tsk : Task)
variable (assigned_cpu : processor num_cpus)

def task_local_to_processor : Prop :=
  ∀ j,
    job_task j = tsk →
    job_local_to_processor sched j assigned_cpu

end NoTaskMigration

section PartitionedSchedule

variable (ts : List Task)
variable (assigned_cpu : Task → processor num_cpus)

def partitioned_schedule : Prop :=
  ∀ tsk,
    tsk ∈ ts →
    task_local_to_processor job_task sched tsk (assigned_cpu tsk)

end PartitionedSchedule

end PartitionedDefs

section SimpleProperties

variable {Job : Type _} [DecidableEq Job]
variable {num_cpus : ℕ}
variable (sched : schedule Job num_cpus)

section NoJobMigrationLemmas

variable (j : Job)

theorem local_jobs_dont_migrate :
    ∀ cpu : processor num_cpus,
      job_local_to_processor sched j cpu → never_migrates sched j := by
  intro cpu H_is_local
  intro t cpu' H_sched_at_t t' cpu'' H_sched_at_t'
  have h1 := H_is_local t cpu' H_sched_at_t
  have h2 := H_is_local t' cpu'' H_sched_at_t'
  rw [h1, h2]

end NoJobMigrationLemmas

end SimpleProperties

end Partitioned

end Prosa.Classic.Model.Schedule.Partitioned.Schedule
