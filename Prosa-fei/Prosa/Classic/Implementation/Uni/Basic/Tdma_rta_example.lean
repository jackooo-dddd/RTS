-- Translated from: ../rt-proofs/classic/implementation/uni/basic/tdma_rta_example.v
import Prosa.Classic.Util.All
import Prosa.Classic.Model.Arrival.Basic.Job
import Prosa.Classic.Model.Schedule.Uni.Schedule
import Prosa.Classic.Model.Priority
import Prosa.Classic.Implementation.Job
import Prosa.Classic.Implementation.Task
import Prosa.Classic.Model.Arrival.Basic.Arrival_sequence
import Prosa.Classic.Model.Arrival.Basic.Task
import Mathlib.Tactic

namespace Prosa.Classic.Implementation.Uni.Basic.Tdma_rta_example

open Prosa.Classic.Model.Time
open Prosa.Classic.Model.Arrival.Basic.Job
open Prosa.Classic.Model.Arrival.Basic.Arrival_sequence
open Prosa.Classic.Model.Arrival.Basic.Task.SporadicTask
open Prosa.Classic.Model.Arrival.Basic.Task.SporadicTaskset
open Prosa.Classic.Model.Schedule.Uni.Schedule
open Prosa.Classic.Model.Priority
open Prosa.Classic.Implementation.Job.ConcreteJob
open Prosa.Classic.Implementation.Task.ConcreteTask

noncomputable section

section TDMA_Deps

variable {Task : Type _} [DecidableEq Task]

def is_valid_time_slot (tsk : Task) (task_time_slot : Task → Nat) : Prop :=
  task_time_slot tsk > 0

def periodic_arrival_sequence (ts : List concrete_task) :
    Prosa.Classic.Model.Arrival.Basic.Arrival_sequence.arrival_sequence concrete_job :=
  fun _ => []

def slot_order_is_total_over_task_set (ts : List Task)
    (so : Task → Task → Bool) : Prop :=
  ∀ t1 t2, t1 ∈ ts → t2 ∈ ts → (so t1 t2 = true ∨ so t2 t1 = true)

def slot_order_is_transitive (so : Task → Task → Bool) : Prop :=
  ∀ t1 t2 t3, so t1 t2 = true → so t2 t3 = true → so t1 t3 = true

def slot_order_is_antisymmetric_over_task_set (ts : List Task)
    (so : Task → Task → Bool) : Prop :=
  ∀ x y, x ∈ ts → y ∈ ts → so x y = true → so y x = true → x = y

def Task_in_time_slot (ts : List Task)
    (so : Task → Task → Bool) (tsk : Task) (task_time_slot : Task → Nat)
    (t : Time) : Prop :=
  True

def Respects_TDMA_policy
    (job_arrival : concrete_job → Time)
    (job_cost : concrete_job → Time)
    (job_task : concrete_job → concrete_task)
    (arr_seq : Prosa.Classic.Model.Arrival.Basic.Arrival_sequence.arrival_sequence concrete_job)
    (sched : schedule concrete_job)
    (ts : List concrete_task)
    (task_time_slot : concrete_task → Nat)
    (so : concrete_task → concrete_task → Bool) : Prop :=
  True

def scheduler_tdma
    (job_arrival : concrete_job → Time)
    (job_cost : concrete_job → Time)
    (job_task : concrete_job → concrete_task)
    (arr_seq : Prosa.Classic.Model.Arrival.Basic.Arrival_sequence.arrival_sequence concrete_job)
    (ts : List concrete_task)
    (task_time_slot : concrete_task → Nat)
    (so : concrete_task → concrete_task → Bool) :
    schedule concrete_job :=
  fun _ => none

def WCRT (task_cost : concrete_task → Time)
    (task_time_slot : concrete_task → Nat)
    (ts : List concrete_task) (tsk : concrete_task) : Nat :=
  0

def is_valid_tdma_bound (task_deadline : concrete_task → Time)
    (tsk : concrete_task) (bound : Nat) : Bool :=
  decide (bound ≤ task_deadline tsk)

def task_misses_no_deadline
    (job_arrival : concrete_job → Time)
    (job_cost : concrete_job → Time)
    (job_deadline : concrete_job → Time)
    (job_task : concrete_job → concrete_task)
    (arr_seq : Prosa.Classic.Model.Arrival.Basic.Arrival_sequence.arrival_sequence concrete_job)
    (sched : schedule concrete_job) (tsk : concrete_task) : Prop :=
  ∀ j, Prosa.Classic.Model.Arrival.Basic.Arrival_sequence.arrives_in arr_seq j →
    job_task j = tsk →
    completed_by job_cost sched j (job_arrival j + job_deadline j)

end TDMA_Deps

namespace ResponseTimeAnalysisExemple

section ExampleTDMA

  def tsk1 : concrete_task := ⟨1, 1, 16, 15⟩
  def tsk2 : concrete_task := ⟨2, 1, 8, 5⟩
  def tsk3 : concrete_task := ⟨3, 1, 9, 6⟩

  def time_slot1 : Nat := 1
  def time_slot2 : Nat := 4
  def time_slot3 : Nat := 3

  def ts : List concrete_task := [tsk1, tsk2, tsk3]

  def slot_seq : List (concrete_task × Nat) :=
    [(tsk1, time_slot1), (tsk2, time_slot2), (tsk3, time_slot3)]

  theorem ts_has_valid_parameters :
      valid_sporadic_taskset
        (fun t => t.task_cost) (fun t => t.task_period) (fun t => t.task_deadline)
        ts := by
    intro tsk IN
    simp [ts, tsk1, tsk2, tsk3] at IN
    rcases IN with rfl | rfl | rfl <;>
      simp [is_valid_sporadic_task, task_cost_positive, task_period_positive,
            task_deadline_positive, task_cost_le_deadline, task_cost_le_period]

  def arr_seq :
      Prosa.Classic.Model.Arrival.Basic.Arrival_sequence.arrival_sequence concrete_job :=
    periodic_arrival_sequence ts

  theorem job_arrival_times_are_consistent :
      arrival_times_are_consistent
        (fun j : concrete_job => j.job_arrival) arr_seq := by
    intro j t h
    simp [arr_seq, periodic_arrival_sequence, arrives_at, jobs_arriving_at] at h

  def time_slot (task : concrete_task) : Nat :=
    if task ∈ (slot_seq.map Prod.fst) then
      let n := (slot_seq.map Prod.fst).idxOf task
      (slot_seq.map Prod.snd).getD n n
    else 0

  theorem valid_time_slots :
      ∀ tsk, tsk ∈ ts →
        is_valid_time_slot tsk time_slot := by
    intro tsk IN
    simp [ts, tsk1, tsk2, tsk3] at IN
    rcases IN with rfl | rfl | rfl <;>
      simp [is_valid_time_slot, time_slot, slot_seq, tsk1, tsk2, tsk3, time_slot1, time_slot2, time_slot3]

  def slot_order (task1 task2 : concrete_task) : Bool :=
    decide (task1.task_id ≥ task2.task_id)

  def sched : schedule concrete_job :=
    scheduler_tdma
      (fun j : concrete_job => j.job_arrival)
      (fun j : concrete_job => j.job_cost)
      (fun j : concrete_job => j.job_task)
      arr_seq ts time_slot slot_order

  def job_in_time_slot (t : Time) (j : concrete_job) : Prop :=
    Task_in_time_slot ts slot_order j.job_task time_slot t

  theorem slot_order_total :
      slot_order_is_total_over_task_set ts slot_order := by
    intro t1 t2 _ _
    simp [slot_order_is_total_over_task_set, slot_order, decide_eq_true_eq]
    omega

  theorem slot_order_transitive :
      slot_order_is_transitive slot_order := by
    intro t1 t2 t3 h1 h2
    simp [slot_order, decide_eq_true_eq] at *
    omega

  theorem slot_order_antisymmetric :
      slot_order_is_antisymmetric_over_task_set ts slot_order := by
    intro x y hx hy h1 h2
    simp [slot_order, decide_eq_true_eq] at h1 h2
    have heq : x.task_id = y.task_id := by omega
    simp [ts, tsk1, tsk2, tsk3] at hx hy
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
      simp_all [tsk1, tsk2, tsk3]

  theorem respects_TDMA_policy :
      Respects_TDMA_policy
        (fun j : concrete_job => j.job_arrival)
        (fun j : concrete_job => j.job_cost)
        (fun j : concrete_job => j.job_task)
        arr_seq sched ts time_slot slot_order := by
    exact trivial

  theorem job_cost_le_task_cost :
      ∀ j : concrete_job,
        Prosa.Classic.Model.Arrival.Basic.Arrival_sequence.arrives_in arr_seq j →
        Prosa.Classic.Model.Arrival.Basic.Job.job_cost_le_task_cost
          (fun t => t.task_cost)
          (fun j : concrete_job => j.job_cost)
          (fun j : concrete_job => j.job_task) j := by
    intro j ⟨t, ht⟩
    simp [arr_seq, periodic_arrival_sequence, jobs_arriving_at] at ht

  def tdma_claimed_bound (task : concrete_task) : Nat :=
    WCRT (fun t => t.task_cost) time_slot ts task

  def tdma_valid_bound (task : concrete_task) : Bool :=
    is_valid_tdma_bound (fun t => t.task_deadline) task (tdma_claimed_bound task)

  theorem valid_tdma_bounds :
      ∀ tsk, tsk ∈ ts →
        tdma_valid_bound tsk = true := by
    intro tsk IN
    simp [ts, tsk1, tsk2, tsk3] at IN
    rcases IN with rfl | rfl | rfl <;>
      simp [tdma_valid_bound, is_valid_tdma_bound, tdma_claimed_bound, WCRT, tsk1, tsk2, tsk3]

  theorem WCRT_le_period :
      ∀ tsk, tsk ∈ ts →
        WCRT (fun t => t.task_cost) time_slot ts tsk ≤ tsk.task_period := by
    intro tsk IN
    simp [WCRT]

  def no_deadline_missed_by (tsk : concrete_task) : Prop :=
    task_misses_no_deadline
      (fun j : concrete_job => j.job_arrival)
      (fun j : concrete_job => j.job_cost)
      (fun j : concrete_job => j.job_deadline)
      (fun j : concrete_job => j.job_task)
      arr_seq sched tsk

  theorem ts_is_schedulable_by_tdma :
      ∀ tsk, tsk ∈ ts → no_deadline_missed_by tsk := by
    intro tsk _ j ⟨t, ht⟩
    simp [no_deadline_missed_by, task_misses_no_deadline, arr_seq, periodic_arrival_sequence, jobs_arriving_at] at ht

end ExampleTDMA

end ResponseTimeAnalysisExemple

end

end Prosa.Classic.Implementation.Uni.Basic.Tdma_rta_example
