-- Translated from: ../rt-proofs/classic/model/schedule/partitioned/schedulability.v
import Prosa.Classic.Util.All
import Prosa.Classic.Model.Arrival.Basic.Arrival_sequence
import Prosa.Classic.Model.Schedule.Global.Schedulability
import Prosa.Classic.Model.Schedule.Global.Basic.Schedule
import Prosa.Classic.Model.Schedule.Partitioned.Schedule
import Prosa.Classic.Model.Schedule.Uni.Schedule
import Prosa.Classic.Model.Schedule.Uni.Schedulability
import Mathlib.Tactic

namespace Prosa.Classic.Model.Schedule.Partitioned.Schedulability

open Prosa.Classic.Model.Time
open Prosa.Classic.Model.Arrival.Basic.Arrival_sequence
open Prosa.Classic.Model.Schedule.Global.Basic.Schedule
open Prosa.Classic.Model.Schedule.Global.Basic.Schedule.Schedule
open Prosa.Classic.Model.Schedule.Global.Schedulability.Schedulability
open Prosa.Classic.Model.Schedule.Partitioned.Schedule.Partitioned

namespace PartitionSchedulability

section PartitionedAsUniprocessor

variable {Task : Type _} [DecidableEq Task]
variable {Job : Type _} [DecidableEq Job]
variable (job_arrival : Job → Time)
variable (job_cost : Job → Time)
variable (job_deadline : Job → Time)
variable (job_task : Job → Task)
variable (arr_seq : arrival_sequence Job)
variable {num_cpus : ℕ}
variable (sched : schedule Job num_cpus)
variable (ts : List Task)
variable (H_all_jobs_from_ts : ∀ j, arrives_in arr_seq j → job_task j ∈ ts)
variable (assigned_cpu : Task → processor num_cpus)
variable (H_partitioned : partitioned_schedule job_task sched ts assigned_cpu)

section SameService

private def partition_of (assigned_cpu : Task → processor num_cpus) (job_task : Job → Task) (j : Job) :
    processor num_cpus :=
  assigned_cpu (job_task j)

variable (j : Job)
variable (H_j_arrives : arrives_in arr_seq j)

include H_all_jobs_from_ts H_partitioned H_j_arrives in
  theorem same_per_processor_service :
    ∀ t1 t2,
      service_during sched j t1 t2 =
      Prosa.Classic.Model.Schedule.Uni.Schedule.service_during
        (fun t => sched (partition_of assigned_cpu job_task j) t) j t1 t2 := by
  intro t1 t2
  unfold service_during
  congr 1
  ext t
  unfold service_at Prosa.Classic.Model.Schedule.Uni.Schedule.service_at
  unfold Prosa.Classic.Model.Schedule.Uni.Schedule.scheduled_at
  unfold partition_of
  have FROMTS := H_all_jobs_from_ts j H_j_arrives
  have PART := H_partitioned (job_task j) FROMTS
  have JLOCAL := PART j rfl
  -- JLOCAL : ∀ t cpu, scheduled_on sched j cpu t = true → cpu = assigned_cpu (job_task j)
  -- Show that for any cpu ≠ cpu₀, scheduled_on sched j cpu t = false
  have h_only_cpu0 : ∀ cpu : Fin num_cpus, cpu ≠ assigned_cpu (job_task j) →
      scheduled_on sched j cpu t = false := by
    intro cpu hne
    cases heq : scheduled_on sched j cpu t
    · rfl
    · exact absurd (JLOCAL t cpu heq) hne
  -- Now case split on whether j is scheduled on cpu₀ at time t
  by_cases h : (sched (assigned_cpu (job_task j)) t == some j) = true
  · -- j IS scheduled on cpu₀
    have h_on : scheduled_on sched j (assigned_cpu (job_task j)) t = true := by
      unfold scheduled_on; exact h
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (assigned_cpu (job_task j)))]
    have h_rest : ∑ x ∈ Finset.univ.erase (assigned_cpu (job_task j)),
        (if scheduled_on sched j x t = true then 1 else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro cpu hcpu
      rw [Finset.mem_erase] at hcpu
      simp [h_only_cpu0 cpu hcpu.1]
    simp [h_on, h_rest, h, Bool.toNat]
  · -- j is NOT scheduled on cpu₀
    simp only [Bool.not_eq_true] at h
    have h_none : ∀ cpu : Fin num_cpus, scheduled_on sched j cpu t = false := by
      intro cpu
      by_cases hcpu : cpu = assigned_cpu (job_task j)
      · subst hcpu; unfold scheduled_on; exact h
      · exact h_only_cpu0 cpu hcpu
    simp only [h, Bool.toNat]
    apply Finset.sum_eq_zero
    intro cpu _
    simp [h_none cpu]

end SameService

section Schedulability

private def schedulable_on
    (job_arrival : Job → Time) (job_cost : Job → Time) (job_deadline : Job → Time)
    (job_task : Job → Task) (arr_seq : arrival_sequence Job)
    {num_cpus : ℕ} (sched : schedule Job num_cpus)
    (tsk : Task) (cpu : processor num_cpus) : Prop :=
  Prosa.Classic.Model.Schedule.Uni.Schedulability.task_misses_no_deadline
    job_arrival job_cost job_deadline job_task arr_seq (fun t => sched cpu t) tsk

private def schedulable
    (job_arrival : Job → Time) (job_cost : Job → Time) (job_deadline : Job → Time)
    (job_task : Job → Task) (arr_seq : arrival_sequence Job)
    {num_cpus : ℕ} (sched : schedule Job num_cpus) (tsk : Task) : Prop :=
  task_misses_no_deadline job_arrival job_cost job_deadline job_task arr_seq sched tsk

variable (H_locally_schedulable :
  ∀ tsk, tsk ∈ ts →
    schedulable_on job_arrival job_cost job_deadline job_task arr_seq sched tsk (assigned_cpu tsk))

include H_all_jobs_from_ts H_partitioned H_locally_schedulable in
  theorem schedulable_at_system_level :
    ∀ tsk, tsk ∈ ts →
      schedulable job_arrival job_cost job_deadline job_task arr_seq sched tsk := by
  intro tsk IN j ARRj JOBtsk
  have SCHED := H_locally_schedulable tsk IN j ARRj JOBtsk
  have SAME := same_per_processor_service job_task arr_seq sched ts H_all_jobs_from_ts assigned_cpu H_partitioned j ARRj
  -- Goal: job_misses_no_deadline ... sched j
  -- = completed job_cost sched j (job_arrival j + job_deadline j)
  -- = service sched j (...) ≥ job_cost j
  -- service = service_during sched j 0 (...)
  -- Use SAME to rewrite service_during
  unfold job_misses_no_deadline completed service
  -- Goal: ∑ t ∈ Ico 0 ..., service_at sched j t ≥ job_cost j
  -- SAME is about service_during which is also ∑ t ∈ Ico ...
  -- Let's use show to match service_during
  show service_during sched j 0 (job_arrival j + job_deadline j) ≥ job_cost j
  rw [SAME]
  -- Now goal: uni.service_during (sched (partition_of ..)) j 0 (...) ≥ job_cost j
  unfold partition_of
  rw [JOBtsk]
  -- Unfold SCHED enough
  unfold Prosa.Classic.Model.Schedule.Uni.Schedulability.job_misses_no_deadline
    Prosa.Classic.Model.Schedule.Uni.Schedulability.completed_by
    Prosa.Classic.Model.Schedule.Uni.Schedulability.service
    Prosa.Classic.Model.Schedule.Uni.Schedulability.service_during
    Prosa.Classic.Model.Schedule.Uni.Schedulability.service_at
    Prosa.Classic.Model.Schedule.Uni.Schedulability.scheduled_at at SCHED
  -- SCHED: job_cost j ≤ ∑ t ∈ Ico ..., if (... == ...) = true then 1 else 0
  -- Goal: uni.service_during ... ≥ job_cost j
  -- Let's convert both to the same form
  suffices h : job_cost j ≤ Prosa.Classic.Model.Schedule.Uni.Schedule.service_during
      (fun t => sched (assigned_cpu tsk) t) j 0 (job_arrival j + job_deadline j) from h
  unfold Prosa.Classic.Model.Schedule.Uni.Schedule.service_during
    Prosa.Classic.Model.Schedule.Uni.Schedule.service_at
    Prosa.Classic.Model.Schedule.Uni.Schedule.scheduled_at
  -- Goal: job_cost j ≤ ∑ t ∈ Ico ..., ((sched (assigned_cpu tsk) t == some j)).toNat
  -- SCHED: job_cost j ≤ ∑ t ∈ Ico ..., if (sched ... t == some j) = true then 1 else 0
  -- Need to show these sums are equal
  convert SCHED using 2
  rename_i t _
  cases h : (sched (assigned_cpu tsk) t == some j) <;> simp [Bool.toNat, beq_iff_eq] at h ⊢

end Schedulability

end PartitionedAsUniprocessor

end PartitionSchedulability

end Prosa.Classic.Model.Schedule.Partitioned.Schedulability
