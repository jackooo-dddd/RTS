-- Translated from: ../rt-proofs/classic/implementation/uni/jitter/arrival_sequence.v
import Prosa.Classic.Model.Arrival.Basic.Arrival_sequence
import Prosa.Classic.Implementation.Uni.Jitter.Task
import Mathlib.Data.List.Basic

namespace Prosa.Classic.Implementation.Uni.Jitter.Arrival_sequence

open Prosa.Classic.Model.Time
open Prosa.Classic.Model.Arrival.Basic.Arrival_sequence
open Prosa.Classic.Implementation.Uni.Jitter.Task.ConcreteTask

namespace ConcreteJob

  structure concrete_job where
    job_id : Nat
    job_arrival : Nat
    job_cost : Nat
    job_deadline : Nat
    job_task : concrete_task
  deriving DecidableEq, Repr

  def job_eqdef (j1 j2 : concrete_job) : Bool :=
    (j1.job_id == j2.job_id) &&
    (j1.job_arrival == j2.job_arrival) &&
    (j1.job_cost == j2.job_cost) &&
    (j1.job_deadline == j2.job_deadline) &&
    (j1.job_task == j2.job_task)

end ConcreteJob

namespace ConcreteArrivalSequence

open ConcreteJob

section PeriodicArrivals

  variable (ts : List concrete_task)

  def add_job (arr_time : Time) (tsk : concrete_task) : Option concrete_job :=
    if tsk.task_period ∣ arr_time then
      some ⟨arr_time / tsk.task_period, arr_time, tsk.task_cost, tsk.task_deadline, tsk⟩
    else
      none

  def periodic_arrival_sequence (t : Time) : List concrete_job :=
    ts.filterMap (add_job t)

end PeriodicArrivals

section Proofs

  variable (ts : List concrete_task)
  variable (H_ts_nodup : ts.Nodup)

  private def arr_seq := periodic_arrival_sequence ts

  theorem periodic_arrivals_are_consistent :
      arrival_times_are_consistent
        (fun j : concrete_job => j.job_arrival)
        (periodic_arrival_sequence ts) := by
    intro j t ARRj
    simp only [arrives_at, jobs_arriving_at, periodic_arrival_sequence, List.mem_filterMap] at ARRj
    obtain ⟨tsk, _, h_add⟩ := ARRj
    simp only [add_job] at h_add
    split at h_add <;> simp at h_add
    exact congrArg concrete_job.job_arrival h_add.symm

  theorem periodic_arrivals_all_jobs_from_taskset :
      ∀ j : concrete_job,
        arrives_in (periodic_arrival_sequence ts) j →
        j.job_task ∈ ts := by
    intro j ⟨t, ARRj⟩
    simp only [jobs_arriving_at, periodic_arrival_sequence, List.mem_filterMap] at ARRj
    obtain ⟨tsk, h_in, h_add⟩ := ARRj
    simp only [add_job] at h_add
    split at h_add <;> simp at h_add
    rw [← h_add]; exact h_in

  def sporadic_task_model_concrete
      (task_period : concrete_task → Time)
      (job_arrival : concrete_job → Time)
      (job_task : concrete_job → concrete_task)
      (arr_seq : arrival_sequence concrete_job) : Prop :=
    ∀ (j j' : concrete_job),
      j ≠ j' →
      arrives_in arr_seq j →
      arrives_in arr_seq j' →
      job_task j = job_task j' →
      job_arrival j ≤ job_arrival j' →
      job_arrival j' ≥ job_arrival j + task_period (job_task j)

  theorem periodic_arrivals_are_sporadic :
      sporadic_task_model_concrete
        (fun tsk => tsk.task_period)
        (fun j => j.job_arrival)
        (fun j => j.job_task)
        (periodic_arrival_sequence ts) := by
    intro j j' DIFF ⟨arr, ARR⟩ ⟨arr', ARR'⟩ SAMEtsk LE
    simp only at SAMEtsk LE ⊢
    simp only [jobs_arriving_at, periodic_arrival_sequence, List.mem_filterMap] at ARR ARR'
    obtain ⟨tsk_j, _, h_add_j⟩ := ARR
    obtain ⟨tsk_j', _, h_add_j'⟩ := ARR'
    simp only [add_job] at h_add_j h_add_j'
    split at h_add_j <;> simp at h_add_j
    split at h_add_j' <;> simp at h_add_j'
    rename_i h_div h_div'
    subst h_add_j; subst h_add_j'
    simp at SAMEtsk
    subst SAMEtsk
    simp at LE ⊢
    obtain ⟨k, hk⟩ := h_div
    obtain ⟨k', hk'⟩ := h_div'
    rw [hk, hk'] at LE ⊢
    -- Goal: tsk_j.task_period * k + tsk_j.task_period ≤ tsk_j.task_period * k'
    -- i.e., p * (k + 1) ≤ p * k'
    by_cases hp : tsk_j.task_period = 0
    · -- period = 0, goal becomes 0 ≤ 0
      simp [hp]
    · -- period > 0
      have hp' : 0 < tsk_j.task_period := Nat.pos_of_ne_zero hp
      rw [← Nat.mul_succ]
      apply Nat.mul_le_mul_left
      have h_le : k ≤ k' := Nat.le_of_mul_le_mul_left LE hp'
      have h_ne : k ≠ k' := by
        intro h_eq
        apply DIFF
        simp [concrete_job.mk.injEq]
        constructor
        · rw [hk, hk', h_eq]
        · rw [hk, hk', h_eq]
      omega

  include H_ts_nodup in
  theorem periodic_arrivals_is_a_set :
      arrival_sequence_is_a_set (periodic_arrival_sequence ts) := by
    intro t
    simp only [jobs_arriving_at, periodic_arrival_sequence]
    apply List.Nodup.filterMap _ H_ts_nodup
    intro a a' b ha ha'
    simp only [Option.mem_def, add_job] at ha ha'
    split_ifs at ha <;> simp at ha
    split_ifs at ha' <;> simp at ha'
    exact congrArg concrete_job.job_task (ha.trans ha'.symm)

  theorem periodic_arrivals_job_cost_le_task_cost :
      ∀ j : concrete_job,
        arrives_in (periodic_arrival_sequence ts) j →
        j.job_cost ≤ j.job_task.task_cost := by
    intro j ⟨t, ARRj⟩
    simp only [jobs_arriving_at, periodic_arrival_sequence, List.mem_filterMap] at ARRj
    obtain ⟨tsk, _, h_add⟩ := ARRj
    simp only [add_job] at h_add
    split at h_add <;> simp at h_add
    rw [← h_add]

  theorem periodic_arrivals_job_deadline_eq_task_deadline :
      ∀ j : concrete_job,
        arrives_in (periodic_arrival_sequence ts) j →
        j.job_deadline = j.job_task.task_deadline := by
    intro j ⟨t, ARRj⟩
    simp only [jobs_arriving_at, periodic_arrival_sequence, List.mem_filterMap] at ARRj
    obtain ⟨tsk, _, h_add⟩ := ARRj
    simp only [add_job] at h_add
    split at h_add <;> simp at h_add
    rw [← h_add]

end Proofs

end ConcreteArrivalSequence

end Prosa.Classic.Implementation.Uni.Jitter.Arrival_sequence
