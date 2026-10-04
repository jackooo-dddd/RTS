-- Authoritative source:
-- ProsaBuddy classic Prosa (prosabuddy commit f692cb7479780cf6009493f373a309e13165201c)
-- source: classic/model/schedule/partitioned/schedulability.v
-- sha256: see Prosa-Shunqi/classic-prosa/comprehensive-classic/file_order.csv (rank 100)

import Prosa.Classic.Util.All
import Prosa.Classic.Model.Arrival.Basic.ArrivalSequence
import Prosa.Classic.Model.Arrival.Basic.Task
import Prosa.Classic.Model.Arrival.Basic.Job
import Prosa.Classic.Model.Schedule.Global.Schedulability
import Prosa.Classic.Model.Schedule.Global.Basic.Schedule
import Prosa.Classic.Model.Schedule.Partitioned.Schedule
import Prosa.Classic.Model.Schedule.Uni.Schedule
import Prosa.Classic.Model.Schedule.Uni.Schedulability

/-!
Partitioned schedulability (Rocq module `PartitionSchedulability`).

Representation notes:
* `uni.*` (the alias `Partitioned.uni` of `UniprocessorSchedule`) and `uni_sched.*` (the module alias of the
  uniprocessor `Schedulability`) are the corresponding Lean namespaces; the alias itself declares nothing.
* `sched cpu` (a global schedule applied to a processor) is a uniprocessor schedule, as in the source.
* `tsk \in ts` is `tsk ∈ ts`; Boolean tests in proposition position are `= true`.
* The section-local `Let`s (`partition_of`, `schedulable_on`, `schedulable`) are unfolded.
* Binder lists follow the Rocq contract.
-/

set_option linter.unusedVariables false

namespace Prosa.Classic.Model.Schedule.Partitioned.Schedulability.PartitionSchedulability

open Prosa.Classic.Model.Time.Time
open Prosa.Classic.Model.Arrival.Basic.ArrivalSequence.ArrivalSequence
open Prosa.Classic.Model.Schedule.Global.Basic.Schedule.Schedule
open Prosa.Classic.Model.Schedule.Global.Schedulability.Schedulability
open Prosa.Classic.Model.Schedule.Partitioned.Schedule.Partitioned
open BigOperators

universe u v

theorem same_per_processor_service {Task : Type u} [DecidableEq Task] {Job : Type v} [DecidableEq Job]
    (job_task : Job → Task) (arr_seq : arrival_sequence Job) {num_cpus : Nat} (sched : schedule Job num_cpus)
    (ts : List Task) (H_all_jobs_from_ts : ∀ j, arrives_in arr_seq j → job_task j ∈ ts)
    (assigned_cpu : Task → processor num_cpus)
    (H_partitioned : partitioned_schedule job_task sched ts assigned_cpu) (j : Job)
    (H_j_arrives : arrives_in arr_seq j) :
    ∀ t1 t2 : time,
      service_during sched j t1 t2 =
        Prosa.Classic.Model.Schedule.Uni.Schedule.UniprocessorSchedule.service_during
          (sched (assigned_cpu (job_task j))) j t1 t2 := by
  intro t1 t2
  unfold service_during Prosa.Classic.Model.Schedule.Uni.Schedule.UniprocessorSchedule.service_during
  apply Finset.sum_congr rfl
  intro t _
  have PART := H_partitioned (job_task j) (H_all_jobs_from_ts j H_j_arrives) j rfl t
  unfold service_at Prosa.Classic.Model.Schedule.Uni.Schedule.UniprocessorSchedule.service_at
    Prosa.Classic.Model.Schedule.Uni.Schedule.UniprocessorSchedule.scheduled_at
  rw [Finset.sum_filter]
  rw [Finset.sum_eq_single (assigned_cpu (job_task j))]
  · simp only [scheduled_on]
    by_cases h : sched (assigned_cpu (job_task j)) t = some j <;> simp [h]
  · intro b _ hb
    cases h : scheduled_on sched j b t
    · simp [h]
    · exact absurd (PART b h) hb
  · intro h; exact absurd (Finset.mem_univ _) h

theorem schedulable_at_system_level {Task : Type u} [DecidableEq Task] {Job : Type v} [DecidableEq Job]
    (job_arrival job_cost job_deadline : Job → time) (job_task : Job → Task) (arr_seq : arrival_sequence Job)
    {num_cpus : Nat} (sched : schedule Job num_cpus) (ts : List Task)
    (H_all_jobs_from_ts : ∀ j, arrives_in arr_seq j → job_task j ∈ ts) (assigned_cpu : Task → processor num_cpus)
    (H_partitioned : partitioned_schedule job_task sched ts assigned_cpu)
    (H_locally_schedulable : ∀ tsk, tsk ∈ ts →
      Prosa.Classic.Model.Schedule.Uni.Schedulability.Schedulability.task_misses_no_deadline job_arrival job_cost
        job_deadline job_task arr_seq (sched (assigned_cpu tsk)) tsk) :
    ∀ tsk, tsk ∈ ts → task_misses_no_deadline job_arrival job_cost job_deadline job_task arr_seq sched tsk := by
  intro tsk IN j ARRj JOBtsk
  have SCHED := H_locally_schedulable tsk IN j ARRj JOBtsk
  have SAME := same_per_processor_service job_task arr_seq sched ts H_all_jobs_from_ts assigned_cpu H_partitioned j
    ARRj 0 (job_arrival j + job_deadline j)
  unfold Prosa.Classic.Model.Schedule.Uni.Schedulability.Schedulability.job_misses_no_deadline at SCHED
  unfold job_misses_no_deadline completed service
  unfold Prosa.Classic.Model.Schedule.Uni.Schedule.UniprocessorSchedule.completed_by
    Prosa.Classic.Model.Schedule.Uni.Schedule.UniprocessorSchedule.service at SCHED
  unfold service_during at SAME
  rw [SAME, JOBtsk]
  exact SCHED

end Prosa.Classic.Model.Schedule.Partitioned.Schedulability.PartitionSchedulability
