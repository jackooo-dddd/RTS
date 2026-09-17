-- Translated from: ../rt-proofs/classic/model/schedule/global/jitter/interference.v
import Prosa.Classic.Util.All
import Prosa.Classic.Model.Arrival.Basic.Task
import Prosa.Classic.Model.Schedule.Global.Jitter.Job
import Prosa.Classic.Model.Schedule.Global.Basic.Interference
import Prosa.Classic.Model.Schedule.Global.Jitter.Schedule
import Prosa.Classic.Model.Schedule.Global.Workload
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

namespace Prosa.Classic.Model.Schedule.Global.Jitter.Interference

open Classical
open Prosa.Classic.Model.Time
open Prosa.Classic.Model.Schedule.Global.Basic.Schedule
open Prosa.Classic.Model.Schedule.Global.Basic.Schedule.Schedule
open Prosa.Classic.Model.Schedule.Global.Jitter.Schedule.ScheduleWithJitter
open Prosa.Classic.Model.Schedule.Global.Jitter.Schedule.ScheduleOfSporadicTaskWithJitter
open Prosa.Classic.Model.Schedule.Global.Workload
open Prosa.Classic.Model.Arrival.Basic.Job
open Prosa.Classic.Model.Arrival.Basic.Arrival_sequence

section InterferenceDefs

variable {sporadic_task : Type _} [DecidableEq sporadic_task]
variable {Job : Type _} [DecidableEq Job]
variable (job_arrival : Job → Time)
variable (job_cost : Job → Time)
variable (job_task : Job → sporadic_task)
variable (job_jitter : Job → Time)
variable (arr_seq : arrival_sequence Job)
variable {num_cpus : ℕ}
variable (sched : schedule Job num_cpus)
variable (j : Job)

section TotalInterference

noncomputable def total_interference (t1 t2 : Time) : ℕ :=
  ∑ t ∈ Finset.Ico t1 t2,
    if backlogged job_arrival job_cost job_jitter sched j t then 1 else 0

end TotalInterference

section JobInterference

variable (job_other : Job)

noncomputable def job_interference (t1 t2 : Time) : ℕ :=
  ∑ t ∈ Finset.Ico t1 t2,
    ∑ cpu : Fin num_cpus,
      if backlogged job_arrival job_cost job_jitter sched j t ∧
         scheduled_on sched job_other cpu t = true then 1 else 0

end JobInterference

section TaskInterference

variable (tsk_other : sporadic_task)

noncomputable def task_interference (t1 t2 : Time) : ℕ :=
  ∑ t ∈ Finset.Ico t1 t2,
    ∑ cpu : Fin num_cpus,
      if backlogged job_arrival job_cost job_jitter sched j t ∧
         task_scheduled_on job_task sched tsk_other cpu t = true then 1 else 0

end TaskInterference

section TaskInterferenceJobList

variable (tsk_other : sporadic_task)

noncomputable def task_interference_joblist (t1 t2 : Time) : ℕ :=
  ∑ j' ∈ ((jobs_scheduled_between sched t1 t2).filter
    (fun j' => decide (job_task j' = tsk_other))).toFinset,
    job_interference job_arrival job_cost job_jitter sched j j' t1 t2

end TaskInterferenceJobList

section BasicLemmas

theorem total_interference_le_delta :
    ∀ t1 t2,
      total_interference job_arrival job_cost job_jitter sched j t1 t2 ≤ t2 - t1 := by
  intro t1 t2
  unfold total_interference
  calc ∑ t ∈ Finset.Ico t1 t2, (if backlogged job_arrival job_cost job_jitter sched j t then 1 else 0)
      ≤ ∑ _t ∈ Finset.Ico t1 t2, 1 := by
        apply Finset.sum_le_sum
        intro t _
        by_cases h : backlogged job_arrival job_cost job_jitter sched j t <;> simp [h]
    _ = t2 - t1 := by
        rw [Finset.sum_const, smul_eq_mul, mul_one, Nat.card_Ico]

theorem job_interference_le_service :
    ∀ j_other t1 t2,
      job_interference job_arrival job_cost job_jitter sched j j_other t1 t2 ≤
        service_during sched j_other t1 t2 := by
  intro j_other t1 t2
  unfold job_interference service_during service_at
  apply Finset.sum_le_sum
  intro t _
  apply Finset.sum_le_sum
  intro cpu _
  by_cases h_back : backlogged job_arrival job_cost job_jitter sched j t
  · by_cases h_on : scheduled_on sched j_other cpu t = true <;> simp [h_back, h_on]
  · by_cases h_on : scheduled_on sched j_other cpu t = true <;> simp [h_back, h_on]

theorem task_interference_le_workload :
    ∀ tsk t1 t2,
      task_interference job_arrival job_cost job_task job_jitter sched j tsk t1 t2 ≤
        workload job_task sched tsk t1 t2 := by
  intro tsk t1 t2
  unfold task_interference workload
  apply Finset.sum_le_sum
  intro t _
  apply Finset.sum_le_sum
  intro cpu _
  unfold task_scheduled_on service_of_task
  cases h_sched : sched cpu t with
  | none =>
    by_cases h_back : backlogged job_arrival job_cost job_jitter sched j t <;> simp [h_back]
  | some j' =>
    simp only []
    by_cases h_back : backlogged job_arrival job_cost job_jitter sched j t
    · simp only [h_back, true_and]
      by_cases h_task : job_task j' = tsk
      · simp [h_task]
      · simp [h_task]
    · simp only [h_back, false_and, ite_false]
      exact Nat.zero_le _

end BasicLemmas

section InterferenceSequentialJobs

variable (H_sequential_jobs : sequential_jobs sched)
include H_sequential_jobs

theorem job_interference_le_delta :
    ∀ j_other t1 delta,
      job_interference job_arrival job_cost job_jitter sched j j_other t1 (t1 + delta) ≤ delta := by
  intro j_other t1 delta
  unfold job_interference
  calc ∑ t ∈ Finset.Ico t1 (t1 + delta),
        ∑ cpu : Fin num_cpus,
          (if backlogged job_arrival job_cost job_jitter sched j t ∧
              scheduled_on sched j_other cpu t = true then 1 else 0)
      ≤ ∑ _t ∈ Finset.Ico t1 (t1 + delta), 1 := by
        apply Finset.sum_le_sum
        intro t _
        by_cases h_exists : ∃ cpu, scheduled_on sched j_other cpu t = true
        · obtain ⟨cpu0, h_on⟩ := h_exists
          calc ∑ cpu : Fin num_cpus,
                (if backlogged job_arrival job_cost job_jitter sched j t ∧
                    scheduled_on sched j_other cpu t = true then 1 else 0)
              ≤ ∑ cpu : Fin num_cpus,
                  (if scheduled_on sched j_other cpu t = true then 1 else 0) := by
                apply Finset.sum_le_sum
                intro cpu _
                by_cases h_back : backlogged job_arrival job_cost job_jitter sched j t
                · by_cases h_on' : scheduled_on sched j_other cpu t = true <;> simp [h_back, h_on']
                · by_cases h_on' : scheduled_on sched j_other cpu t = true <;> simp [h_back, h_on']
            _ ≤ 1 := by
                exact service_at_most_one sched j_other H_sequential_jobs t
        · push_neg at h_exists
          have h_zero : (∑ cpu : Fin num_cpus,
              (if backlogged job_arrival job_cost job_jitter sched j t ∧
                  scheduled_on sched j_other cpu t = true then 1 else 0 : ℕ)) = 0 := by
            apply Finset.sum_eq_zero
            intro cpu _
            have h_not_on : ¬(scheduled_on sched j_other cpu t = true) := h_exists cpu
            simp [h_not_on]
          rw [h_zero]; exact Nat.zero_le 1
    _ = delta := by
        rw [Finset.sum_const, smul_eq_mul, mul_one]
        simp [Nat.card_Ico]

end InterferenceSequentialJobs

section BoundUsingPerJobInterference

theorem interference_le_interference_joblist :
    ∀ tsk t1 t2,
      task_interference job_arrival job_cost job_task job_jitter sched j tsk t1 t2 ≤
        task_interference_joblist job_arrival job_cost job_task job_jitter sched j tsk t1 t2 := by
  intro tsk t1 t2
  unfold task_interference task_interference_joblist job_interference
  rw [Finset.sum_comm (s := ((jobs_scheduled_between sched t1 t2).filter
    (fun j' => decide (job_task j' = tsk))).toFinset)]
  apply Finset.sum_le_sum
  intro t ht
  rw [Finset.sum_comm (s := ((jobs_scheduled_between sched t1 t2).filter
    (fun j' => decide (job_task j' = tsk))).toFinset)]
  apply Finset.sum_le_sum
  intro cpu _
  by_cases h_back : backlogged job_arrival job_cost job_jitter sched j t
  · simp only [h_back, true_and]
    by_cases h_task_sched : task_scheduled_on job_task sched tsk cpu t = true
    · simp only [h_task_sched, ite_true]
      unfold task_scheduled_on at h_task_sched
      cases h_sched_val : sched cpu t with
      | none => simp [h_sched_val] at h_task_sched
      | some j' =>
        simp [h_sched_val] at h_task_sched
        have h_j'_on : scheduled_on sched j' cpu t = true := by
          unfold scheduled_on
          simp [h_sched_val]
        have h_j'_mem_jsb : j' ∈ jobs_scheduled_between sched t1 t2 := by
          unfold jobs_scheduled_between
          rw [List.mem_dedup]
          rw [Finset.mem_Ico] at ht
          apply Prosa.Util.Bigcat.mem_bigcat_nat (x := j') (m := t1) (n := t2) (j := t)
          · exact ⟨ht.1, ht.2⟩
          · rw [mem_scheduled_jobs_eq_scheduled]
            exact ⟨cpu, h_j'_on⟩
        have h_j'_in_filt : j' ∈ ((jobs_scheduled_between sched t1 t2).filter
            (fun j' => decide (job_task j' = tsk))).toFinset := by
          rw [List.mem_toFinset, List.mem_filter]
          exact ⟨h_j'_mem_jsb, by simp [h_task_sched]⟩
        have h_term : (if scheduled_on sched j' cpu t = true then 1 else 0 : ℕ) = 1 := by
          simp [h_j'_on]
        calc (1 : ℕ) = (if scheduled_on sched j' cpu t = true then 1 else 0) := h_term.symm
          _ ≤ ∑ j'_1 ∈ ((jobs_scheduled_between sched t1 t2).filter
                (fun j' => decide (job_task j' = tsk))).toFinset,
                (if scheduled_on sched j'_1 cpu t = true then 1 else 0) :=
              Finset.single_le_sum (f := fun j'_1 => if scheduled_on sched j'_1 cpu t = true then 1 else 0)
                (fun i _ => by simp only []; split_ifs <;> omega) h_j'_in_filt
    · simp only [h_task_sched]
      exact Nat.zero_le _
  · simp only [h_back, false_and, ite_false]
    exact Nat.zero_le _

end BoundUsingPerJobInterference

end InterferenceDefs

end Prosa.Classic.Model.Schedule.Global.Jitter.Interference
