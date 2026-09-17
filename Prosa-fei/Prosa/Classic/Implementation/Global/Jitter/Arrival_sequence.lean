-- Translated from: ../rt-proofs/classic/implementation/global/jitter/arrival_sequence.v
import Prosa.Classic.Model.Arrival.Basic.Arrival_sequence
import Prosa.Classic.Model.Arrival.Basic.Job
import Prosa.Classic.Model.Arrival.Basic.Task
import Prosa.Classic.Model.Schedule.Global.Jitter.Job
import Prosa.Classic.Implementation.Global.Jitter.Task
import Mathlib.Tactic

namespace Prosa.Classic.Implementation.Global.Jitter.Arrival_sequence

namespace ConcreteArrivalSequence

open Prosa.Classic.Model.Time
open Prosa.Classic.Model.Arrival.Basic.Arrival_sequence
open Prosa.Classic.Model.Arrival.Basic.Job
open Prosa.Classic.Model.Arrival.Basic.Task.SporadicTask
open Prosa.Classic.Model.Arrival.Basic.Task.SporadicTaskset
open Prosa.Classic.Model.Schedule.Global.Jitter.Job
open Prosa.Classic.Implementation.Global.Jitter.Task.ConcreteTask

section Defs

open Defs

structure concrete_job where
  job_id : Nat
  job_arrival : Time
  job_cost : Time
  job_deadline : Time
  job_jitter : Time
  job_task : concrete_task
  deriving DecidableEq

def job_eqdef (j1 j2 : concrete_job) : Bool :=
  (j1.job_id == j2.job_id) &&
  (j1.job_arrival == j2.job_arrival) &&
  (j1.job_cost == j2.job_cost) &&
  (j1.job_deadline == j2.job_deadline) &&
  (j1.job_jitter == j2.job_jitter) &&
  (j1.job_task == j2.job_task)

end Defs

def sporadic_task_model
    (task_period : Defs.concrete_task → Time)
    (job_arrival : concrete_job → Time) (job_task : concrete_job → Defs.concrete_task)
    (arr_seq : arrival_sequence concrete_job) : Prop :=
  ∀ (j j' : concrete_job),
    j ≠ j' →
    arrives_in arr_seq j →
    arrives_in arr_seq j' →
    job_task j = job_task j' →
    job_arrival j ≤ job_arrival j' →
    job_arrival j' ≥ job_arrival j + task_period (job_task j)

section PeriodicArrivals

  open Defs

  variable (ts : List concrete_task)

  def add_job (arr_time : Time) (tsk : concrete_task) : Option concrete_job :=
    if tsk.task_period ∣ arr_time then
      some ⟨arr_time / tsk.task_period, arr_time, tsk.task_cost, tsk.task_deadline, tsk.task_jitter, tsk⟩
    else
      none

  def periodic_arrival_sequence (t : Time) : List concrete_job :=
    ts.filterMap (add_job t)

end PeriodicArrivals

section Proofs

  open Defs

  variable (ts : List concrete_task)
  variable (H_valid_task_parameters :
    valid_sporadic_taskset (fun t => t.task_cost) (fun t => t.task_period) (fun t => t.task_deadline) ts)
  variable (H_ts_nodup : ts.Nodup)

  private def arr_seq := periodic_arrival_sequence ts

  theorem periodic_arrivals_are_consistent :
      arrival_times_are_consistent
        (fun j : concrete_job => j.job_arrival)
        (arr_seq ts) := by
    intro j t hj
    show j.job_arrival = t
    have hj' : j ∈ (periodic_arrival_sequence ts t) := hj
    simp only [periodic_arrival_sequence, List.mem_filterMap] at hj'
    obtain ⟨tsk, _, htsk⟩ := hj'
    simp only [add_job] at htsk
    split at htsk
    · next h => injection htsk with htsk; rw [← htsk]
    · exact absurd htsk nofun

  theorem periodic_arrivals_all_jobs_from_taskset :
      ∀ j,
        arrives_in (arr_seq ts) j →
        j.job_task ∈ ts := by
    intro j ⟨t, hj⟩
    simp only [jobs_arriving_at, arr_seq, periodic_arrival_sequence] at hj
    rw [List.mem_filterMap] at hj
    obtain ⟨tsk, htsk_in, htsk_some⟩ := hj
    simp only [add_job] at htsk_some
    split_ifs at htsk_some with h <;> simp at htsk_some
    rw [← htsk_some]
    exact htsk_in

  include H_valid_task_parameters in
  theorem periodic_arrivals_valid_job_parameters :
      ∀ j,
        arrives_in (arr_seq ts) j →
        valid_sporadic_job_with_jitter
          (fun t => t.task_cost) (fun t => t.task_deadline) (fun t => t.task_jitter)
          (fun j : concrete_job => j.job_cost) (fun j : concrete_job => j.job_deadline)
          (fun j : concrete_job => j.job_task) (fun j : concrete_job => j.job_jitter)
          j := by
    intro j ⟨t, hj⟩
    simp only [jobs_arriving_at, arr_seq, periodic_arrival_sequence] at hj
    rw [List.mem_filterMap] at hj
    obtain ⟨tsk, htsk_in, htsk_some⟩ := hj
    simp only [add_job] at htsk_some
    split_ifs at htsk_some with h <;> simp at htsk_some
    have hparams := H_valid_task_parameters tsk htsk_in
    simp only [is_valid_sporadic_task, task_cost_positive, task_period_positive,
      task_deadline_positive, task_cost_le_deadline, task_cost_le_period] at hparams
    obtain ⟨hcost_pos, _, hdeadline_pos, hcost_le_deadline, _⟩ := hparams
    simp only [valid_sporadic_job_with_jitter, valid_sporadic_job, valid_realtime_job,
      job_cost_positive, job_cost_le_deadline, job_deadline_positive,
      job_cost_le_task_cost, job_deadline_eq_task_deadline,
      job_jitter_leq_task_jitter]
    subst htsk_some
    exact ⟨⟨⟨hcost_pos, hcost_le_deadline, hdeadline_pos⟩, Nat.le_refl _, rfl⟩, Nat.le_refl _⟩

  theorem periodic_arrivals_are_sporadic :
      sporadic_task_model
        (fun t => t.task_period)
        (fun j : concrete_job => j.job_arrival)
        (fun j : concrete_job => j.job_task)
        (arr_seq ts) := by
    intro j j' hneq ⟨arr, harr⟩ ⟨arr', harr'⟩ hsame hle
    simp only [jobs_arriving_at, arr_seq, periodic_arrival_sequence] at harr harr'
    rw [List.mem_filterMap] at harr harr'
    obtain ⟨tsk_j, _, hj_some⟩ := harr
    obtain ⟨tsk_j', _, hj'_some⟩ := harr'
    simp only [add_job] at hj_some hj'_some
    split_ifs at hj_some with hdiv_j <;> simp at hj_some
    split_ifs at hj'_some with hdiv_j' <;> simp at hj'_some
    subst hj_some; subst hj'_some
    simp at hsame
    subst hsame
    simp at hle ⊢
    simp only [ne_eq, concrete_job.mk.injEq, not_and] at hneq
    obtain ⟨k, hk⟩ := hdiv_j
    obtain ⟨k', hk'⟩ := hdiv_j'
    rw [hk, hk'] at hle hneq ⊢
    by_cases hperiod : tsk_j.task_period = 0
    · simp [hperiod]
    · have hperiod_pos : tsk_j.task_period > 0 := Nat.pos_of_ne_zero hperiod
      have hk_ne : k ≠ k' := by
        intro heq; subst heq; simp at hneq
      have hk_le : k ≤ k' := Nat.le_of_mul_le_mul_left hle hperiod_pos
      have hk_lt : k < k' := Nat.lt_of_le_of_ne hk_le hk_ne
      calc tsk_j.task_period * k'
          ≥ tsk_j.task_period * (k + 1) := by
            apply Nat.mul_le_mul_left; omega
        _ = tsk_j.task_period * k + tsk_j.task_period := by ring

  include H_ts_nodup in
  theorem periodic_arrivals_is_a_set :
      arrival_sequence_is_a_set (arr_seq ts) := by
    intro t
    simp only [arr_seq, jobs_arriving_at, periodic_arrival_sequence]
    apply List.Nodup.filterMap _ H_ts_nodup
    intro a a' b ha ha'
    simp only [Option.mem_def, add_job] at ha ha'
    split_ifs at ha <;> simp at ha
    split_ifs at ha' <;> simp at ha'
    exact congrArg concrete_job.job_task (ha.trans ha'.symm)

end Proofs

end ConcreteArrivalSequence

end Prosa.Classic.Implementation.Global.Jitter.Arrival_sequence
