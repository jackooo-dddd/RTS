-- Authoritative source:
-- ProsaBuddy classic Prosa (prosabuddy commit f692cb7479780cf6009493f373a309e13165201c)
-- source: classic/implementation/arrival_sequence.v
-- sha256: see Prosa-Shunqi/classic-prosa/comprehensive-classic/file_order.csv (rank 62)

import Prosa.Classic.Util.All
import Prosa.Classic.Model.Arrival.Basic.ArrivalSequence
import Prosa.Classic.Model.Arrival.Basic.Job
import Prosa.Classic.Model.Arrival.Basic.Task
import Prosa.Classic.Model.Arrival.Basic.TaskArrival
import Prosa.Classic.Implementation.Task
import Prosa.Classic.Implementation.Job

/-!
Periodic arrival sequences of concrete tasks (Rocq module `ConcreteArrivalSequence`).

Representation notes:
* MathComp's `d %| m` is `decide (d ∣ m)` (both mean `m %% d == 0`, including `d = 0`); `%/` is `/`;
  `Build_concrete_job` is the structure constructor `concrete_job.mk`; record projections are the structure
  fields; `pmap f s` is `s.filterMap f`; the task set `ts` used as a sequence is `ts.val`.
* The section-local `Let arr_seq := periodic_arrival_sequence ts` is unfolded.
* Binder lists follow the Rocq contract; `periodic_arrivals_valid_job_parameters` uses `valid_sporadic_job`.
-/

set_option linter.unusedVariables false

namespace Prosa.Classic.Implementation.ArrivalSequence.ConcreteArrivalSequence

open Prosa.Classic.Model.Time.Time
open Prosa.Classic.Model.Arrival.Basic.ArrivalSequence.ArrivalSequence
open Prosa.Classic.Model.Arrival.Basic.Task.SporadicTaskset
open Prosa.Classic.Model.Arrival.Basic.Task.SporadicTask
open Prosa.Classic.Model.Arrival.Basic.Job.Job
open Prosa.Classic.Model.Arrival.Basic.TaskArrival.TaskArrival
open Prosa.Classic.Implementation.Task.ConcreteTask
open Prosa.Classic.Implementation.Job.ConcreteJob

def add_job (arr_time : time) (tsk : concrete_task) : Option concrete_job :=
  if decide (tsk.task_period ∣ arr_time) then
    some (concrete_job.mk (arr_time / tsk.task_period) arr_time tsk.task_cost tsk.task_deadline tsk)
  else none

def periodic_arrival_sequence (ts : concrete_taskset) (t : time) : List concrete_job :=
  ts.val.filterMap (add_job t)

/-- LEAN_HELPER: the jobs arriving at `t` are the jobs added for the tasks of `ts` whose period divides `t`. -/
private theorem mem_arrivals (ts : concrete_taskset) (t : time) (j : concrete_job) :
    j ∈ jobs_arriving_at (periodic_arrival_sequence ts) t ↔
      ∃ tsk ∈ ts.val, tsk.task_period ∣ t ∧
        j = concrete_job.mk (t / tsk.task_period) t tsk.task_cost tsk.task_deadline tsk := by
  simp only [jobs_arriving_at, periodic_arrival_sequence, List.mem_filterMap, add_job]
  constructor
  · rintro ⟨tsk, IN, h⟩
    split at h
    · rename_i hd; exact ⟨tsk, IN, by simpa using hd, (Option.some.inj h).symm⟩
    · exact absurd h (by simp)
  · rintro ⟨tsk, IN, hd, rfl⟩
    exact ⟨tsk, IN, by simp [hd]⟩

theorem periodic_arrivals_are_consistent (ts : concrete_taskset) :
    arrival_times_are_consistent concrete_job.job_arrival (periodic_arrival_sequence ts) := by
  intro j t ARRj
  simp only [arrives_at, decide_eq_true_eq] at ARRj
  obtain ⟨tsk, _, _, rfl⟩ := (mem_arrivals ts t j).mp ARRj
  rfl

theorem periodic_arrivals_all_jobs_from_taskset (ts : concrete_taskset) :
    ∀ j, arrives_in (periodic_arrival_sequence ts) j → j.job_task ∈ ts := by
  intro j ⟨t, ARRj⟩
  obtain ⟨tsk, IN, _, rfl⟩ := (mem_arrivals ts t j).mp ARRj
  exact IN

theorem periodic_arrivals_valid_job_parameters (ts : concrete_taskset)
    (H_valid_task_parameters : valid_sporadic_taskset concrete_task.task_cost concrete_task.task_period
      concrete_task.task_deadline ts.val) :
    ∀ j, arrives_in (periodic_arrival_sequence ts) j →
      valid_sporadic_job concrete_task.task_cost concrete_task.task_deadline concrete_job.job_cost
        concrete_job.job_deadline concrete_job.job_task j := by
  intro j ⟨t, ARRj⟩
  obtain ⟨tsk, IN, _, rfl⟩ := (mem_arrivals ts t j).mp ARRj
  obtain ⟨hc, _, hd, hcd, _⟩ := H_valid_task_parameters tsk IN
  simp only [task_cost_positive, task_deadline_positive, task_cost_le_deadline, decide_eq_true_eq] at hc hd hcd
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩ <;>
    simp [job_cost_positive, job_cost_le_deadline, job_deadline_positive, job_cost_le_task_cost,
      job_deadline_eq_task_deadline, hc, hd, hcd]

theorem periodic_arrivals_are_sporadic (ts : concrete_taskset) :
    sporadic_task_model concrete_task.task_period concrete_job.job_arrival concrete_job.job_task
      (periodic_arrival_sequence ts) := by
  intro j j' DIFF ⟨arr, ARR⟩ ⟨arr', ARR'⟩ SAMEtsk LE
  obtain ⟨tsk, _, d1, rfl⟩ := (mem_arrivals ts arr j).mp ARR
  obtain ⟨tsk', _, d2, rfl⟩ := (mem_arrivals ts arr' j').mp ARR'
  simp only at SAMEtsk LE ⊢
  subst SAMEtsk
  obtain ⟨k, rfl⟩ := d1
  obtain ⟨k', rfl⟩ := d2
  rcases Nat.lt_or_ge k k' with hk | hk
  · have := Nat.mul_le_mul_left tsk.task_period hk
    rw [Nat.mul_succ] at this
    exact this
  · have hkk : k = k' := by
      rcases Nat.eq_zero_or_pos tsk.task_period with h0 | hp
      · exfalso; apply DIFF; simp [h0]
      · exact Nat.le_antisymm (Nat.le_of_mul_le_mul_left LE hp) hk
    subst hkk
    exact absurd rfl DIFF

theorem periodic_arrivals_is_a_set (ts : concrete_taskset)
    (H_valid_task_parameters : valid_sporadic_taskset concrete_task.task_cost concrete_task.task_period
      concrete_task.task_deadline ts.val) :
    arrival_sequence_is_a_set (periodic_arrival_sequence ts) := by
  intro t
  apply ts.nodup.filterMap
  intro a a' b hb hb'
  simp only [add_job, Option.mem_def] at hb hb'
  split at hb <;> split at hb' <;> simp_all
  rw [← hb] at hb'
  exact (concrete_job.mk.inj hb').2.2.2.2.symm

end Prosa.Classic.Implementation.ArrivalSequence.ConcreteArrivalSequence
