-- Translated from: ../rt-proofs/classic/implementation/uni/susp/dynamic/arrival_sequence.v
import Prosa.Classic.Model.Arrival.Basic.Arrival_sequence
import Prosa.Classic.Model.Arrival.Basic.Job
import Prosa.Classic.Implementation.Uni.Susp.Dynamic.Task

namespace Prosa.Classic.Implementation.Uni.Susp.Dynamic.Arrival_sequence

namespace ConcreteArrivalSequence

open Prosa.Classic.Model.Time
open Prosa.Classic.Model.Arrival.Basic.Arrival_sequence
open Prosa.Classic.Model.Arrival.Basic.Task.SporadicTask
open Prosa.Classic.Model.Arrival.Basic.Task.SporadicTaskset
open Prosa.Classic.Implementation.Uni.Susp.Dynamic.Task.ConcreteTask
open Prosa.Classic.Model.Arrival.Basic.Job

structure concrete_job where
  job_id : Nat
  job_arrival : Nat
  job_cost : Nat
  job_deadline : Nat
  job_task : concrete_task
deriving DecidableEq

def job_eqdef (j1 j2 : concrete_job) : Bool :=
  (j1.job_id == j2.job_id) &&
  (j1.job_arrival == j2.job_arrival) &&
  (j1.job_cost == j2.job_cost) &&
  (j1.job_deadline == j2.job_deadline) &&
  (j1.job_task == j2.job_task)

def sporadic_task_model
    (task_period : concrete_task → Time)
    (job_arrival_fn : concrete_job → Time)
    (job_task_fn : concrete_job → concrete_task)
    (as : arrival_sequence concrete_job) :=
  ∀ (j j' : concrete_job),
    j ≠ j' →
    arrives_in as j →
    arrives_in as j' →
    job_task_fn j = job_task_fn j' →
    job_arrival_fn j ≤ job_arrival_fn j' →
    job_arrival_fn j' ≥ job_arrival_fn j + task_period (job_task_fn j)

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
variable (H_valid_task_parameters :
  valid_sporadic_taskset
    concrete_task.task_cost concrete_task.task_period concrete_task.task_deadline ts)
variable (H_ts_nodup : ts.Nodup)

include H_valid_task_parameters

private abbrev arr_seq' := periodic_arrival_sequence ts

theorem periodic_arrivals_are_consistent :
    arrival_times_are_consistent
      concrete_job.job_arrival (arr_seq' ts) := by
  intro j t ARRj
  simp only [arrives_at, jobs_arriving_at, arr_seq', periodic_arrival_sequence,
    List.mem_filterMap] at ARRj
  obtain ⟨tsk, _, h_some⟩ := ARRj
  simp only [add_job] at h_some
  split at h_some <;> simp at h_some
  rw [← h_some]

theorem periodic_arrivals_all_jobs_from_taskset :
    ∀ j,
      arrives_in (arr_seq' ts) j →
      j.job_task ∈ ts := by
  intro j ⟨t, ARRj⟩
  simp only [jobs_arriving_at, arr_seq', periodic_arrival_sequence,
    List.mem_filterMap] at ARRj
  obtain ⟨tsk, h_in, h_some⟩ := ARRj
  simp only [add_job] at h_some
  split at h_some <;> simp at h_some
  rw [← h_some]
  exact h_in

theorem periodic_arrivals_valid_job_parameters :
    ∀ j,
      arrives_in (arr_seq' ts) j →
      valid_sporadic_job
        concrete_task.task_cost concrete_task.task_deadline
        concrete_job.job_cost concrete_job.job_deadline concrete_job.job_task j := by
  intro j ⟨t, ARRj⟩
  simp only [jobs_arriving_at, arr_seq', periodic_arrival_sequence,
    List.mem_filterMap] at ARRj
  obtain ⟨tsk, h_in, h_some⟩ := ARRj
  simp only [add_job] at h_some
  split at h_some <;> simp at h_some
  subst h_some
  have PARAMS := H_valid_task_parameters tsk h_in
  simp only [is_valid_sporadic_task, task_cost_positive, task_period_positive,
    task_deadline_positive, task_cost_le_deadline, task_cost_le_period] at PARAMS
  obtain ⟨h_cost_pos, _, h_dl_pos, h_cost_le_dl, _⟩ := PARAMS
  exact ⟨⟨h_cost_pos, h_cost_le_dl, h_dl_pos⟩, le_refl _, rfl⟩

theorem periodic_arrivals_are_sporadic :
    sporadic_task_model
      concrete_task.task_period concrete_job.job_arrival
      concrete_job.job_task (arr_seq' ts) := by
  intro j j' DIFF ⟨arr, ARR⟩ ⟨arr', ARR'⟩ SAMEtsk LE
  simp only [jobs_arriving_at, arr_seq', periodic_arrival_sequence,
    List.mem_filterMap] at ARR ARR'
  obtain ⟨tsk_j, _, h_somej⟩ := ARR
  obtain ⟨tsk_j', _, h_somej'⟩ := ARR'
  simp only [add_job] at h_somej h_somej'
  split at h_somej <;> simp at h_somej
  split at h_somej' <;> simp at h_somej'
  rename_i h_div h_div'
  subst h_somej; subst h_somej'
  simp at SAMEtsk
  subst SAMEtsk
  simp at LE ⊢
  have h_arr_ne : arr ≠ arr' := by
    intro h_eq; apply DIFF; subst h_eq; rfl
  obtain ⟨k, hk⟩ := h_div
  obtain ⟨k', hk'⟩ := h_div'
  subst hk; subst hk'
  have h_k_ne : k ≠ k' := by
    intro h_eq; apply h_arr_ne; rw [h_eq]
  have h_k_lt : k < k' := by
    rcases Nat.lt_or_ge k k' with h | h
    · exact h
    · exfalso
      have h1 : tsk_j.task_period * k' ≤ tsk_j.task_period * k :=
        Nat.mul_le_mul_left _ h
      have h2 : tsk_j.task_period * k = tsk_j.task_period * k' :=
        Nat.le_antisymm LE h1
      apply h_arr_ne; exact h2
  have h_kp1 : k + 1 ≤ k' := h_k_lt
  calc tsk_j.task_period * k + tsk_j.task_period
      = tsk_j.task_period * (k + 1) := by ring
    _ ≤ tsk_j.task_period * k' := Nat.mul_le_mul_left _ h_kp1

include H_ts_nodup in
theorem periodic_arrivals_is_a_set :
    arrival_sequence_is_a_set (arr_seq' ts) := by
  intro t
  simp only [arr_seq', jobs_arriving_at, periodic_arrival_sequence]
  apply List.Nodup.filterMap _ H_ts_nodup
  intro a a' b ha ha'
  simp only [Option.mem_def, add_job] at ha ha'
  split_ifs at ha <;> simp at ha
  split_ifs at ha' <;> simp at ha'
  exact congrArg concrete_job.job_task (ha.trans ha'.symm)

end Proofs

end ConcreteArrivalSequence

end Prosa.Classic.Implementation.Uni.Susp.Dynamic.Arrival_sequence
