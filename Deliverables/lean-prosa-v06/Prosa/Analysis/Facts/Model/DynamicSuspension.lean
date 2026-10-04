-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/facts/model/dynamic_suspension.v

import Prosa.Analysis.Facts.Suspension
import Prosa.Model.Task.Suspension.Dynamic
import Prosa.Model.Task.Arrival.Curves
import Prosa.Util.Sum

namespace Prosa.Analysis.Facts.Model.DynamicSuspension

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Behavior.Time
open Prosa.Model.Task.Concept
open Prosa.Model.Task.Arrivals
open Prosa.Model.Task.Arrival.Curves
open Prosa.Model.Readiness.Suspension
open Prosa.Model.Task.Suspension.Dynamic
open Prosa.Analysis.Facts.Suspension
open Prosa.Util.Sum
open scoped BigOperators

/-! Under the dynamic self-suspension model, the total self-suspension of a job, and of all jobs of a task, within
an interval is bounded.

Binders follow the elaborated source types: each statement takes the section inputs and hypotheses it uses, in
their elaborated order (the unused validity hypotheses of the arrival sequence and the schedule are absent).
Representation: a Boolean in `Prop` position is `= true`; the interval sum `\sum_(t1 <= t < t2) F t` is the
`Finset.Ico` sum over `Nat`; `\sum_(j <- xs) F j` is `sumSeq xs F`; `nat_of_bool` is `Bool.toNat`. -/

/-- LEAN_HELPER: appending one entry to a list fold of additions. -/
private theorem foldr_add_snoc (l : List Nat) (x : Nat) :
    List.foldr Nat.add 0 (l ++ [x]) = List.foldr Nat.add 0 l + x := by
  induction l with
  | nil => show x + 0 = 0 + x; omega
  | cons a l ih =>
    rw [List.cons_append, List.foldr_cons, List.foldr_cons, ih]
    show a + (List.foldr Nat.add 0 l + x) = a + List.foldr Nat.add 0 l + x
    omega

/-- LEAN_HELPER: the ascending list fold of the total suspension as a finite sum over `range`. -/
private theorem foldr_range'_eq_sum (g : Nat → Nat) : ∀ m : Nat,
    List.foldr Nat.add 0 ((List.range' 0 m).map g) = ∑ r ∈ Finset.range m, g r
  | 0 => by simp
  | m + 1 => by
    rw [Finset.sum_range_succ, ← foldr_range'_eq_sum g m, List.range'_concat, List.map_append,
      List.map_cons, List.map_nil, foldr_add_snoc]
    simp

/-- LEAN_HELPER: exchanging an interval sum with a sequence sum. -/
private theorem sum_sumSeq_comm {J : Type _} (s : Finset Nat) (xs : List J) (f : Nat → J → Nat) :
    ∑ t ∈ s, sumSeq xs (f t) = sumSeq xs (fun j => ∑ t ∈ s, f t j) := by
  induction xs with
  | nil => simp [sumSeq]
  | cons x xs ih =>
    simp only [sumSeq, List.map_cons, List.sum_cons] at ih ⊢
    rw [Finset.sum_add_distrib, ih]

/-- LEAN_HELPER: a sequence sum of terms bounded by `c` is at most the length times `c`. -/
private theorem sumSeq_le_length_mul {J : Type _} (xs : List J) (F : J → Nat) (c : Nat)
    (h : ∀ j, j ∈ xs → F j ≤ c) : sumSeq xs F ≤ xs.length * c := by
  induction xs with
  | nil => simp [sumSeq]
  | cons x xs ih =>
    simp only [sumSeq, List.map_cons, List.sum_cons, List.length_cons] at ih ⊢
    have hx := h x (List.mem_cons_self)
    have hxs := ih (fun j hj => h j (List.mem_cons_of_mem x hj))
    rw [Nat.succ_mul]
    omega

section TotalSuspensionBounded

variable {Task : TaskType} [DecidableEq Task]
variable {Job : JobType} [DecidableEq Job]

/-- Under valid dynamic suspensions, the total suspension of a job of `tsk` within `[t1, t1 + Δ)` is at most the
task's total suspension bound. -/
theorem job_suspension_bounded [TaskTotalSuspension Task] [JobTask Job Task] [JobArrival Job] [JobCost Job]
    [JobSuspension Job] :
    valid_dynamic_suspensions (Job := Job) (Task := Task) →
    ∀ (PState : ProcessorState Job) (sched : schedule PState) (tsk : Task) (t1 : instant) (Δ : duration)
      (j : Job), job_of_task tsk j = true →
      ∑ t ∈ Finset.Ico (α := Nat) t1 (t1 + Δ), (suspended sched j t).toNat ≤ task_total_suspension tsk := by
  intro hvalid PState sched tsk t1 Δ j hjt
  have htask : job_task j = tsk := of_decide_eq_true hjt
  have key : ∀ t, (suspended sched j t).toNat =
      ∑ r ∈ Finset.range (job_cost j),
        (if service sched j t = r then (suspended sched j t).toNat else 0) := by
    intro t
    rw [Finset.sum_ite_eq]
    cases hs : suspended sched j t with
    | false => simp
    | true =>
      have hp := suspended_implies_pending sched j t hs
      unfold pending at hp
      have hnc := (Bool.and_eq_true_iff.mp hp).2
      have hlt : service sched j t < job_cost j := by
        unfold completed_by at hnc
        simp only [Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not, Nat.not_le] at hnc
        exact hnc
      simp [Finset.mem_range, hlt]
  calc ∑ t ∈ Finset.Ico (α := Nat) t1 (t1 + Δ), (suspended sched j t).toNat
      = ∑ t ∈ Finset.Ico (α := Nat) t1 (t1 + Δ), ∑ r ∈ Finset.range (job_cost j),
          (if service sched j t = r then (suspended sched j t).toNat else 0) :=
        Finset.sum_congr rfl (fun t _ => key t)
    _ = ∑ r ∈ Finset.range (job_cost j), ∑ t ∈ Finset.Ico (α := Nat) t1 (t1 + Δ),
          (if service sched j t = r then (suspended sched j t).toNat else 0) := Finset.sum_comm
    _ ≤ ∑ r ∈ Finset.range (job_cost j), job_suspension j r :=
        Finset.sum_le_sum fun r _ => suspension_bounded_in_interval sched j t1 (t1 + Δ) r
    _ = total_suspension j := by
        unfold total_suspension
        rw [Nat.sub_zero, foldr_range'_eq_sum]
    _ ≤ task_total_suspension (job_task (Task := Task) j) := hvalid j
    _ = task_total_suspension tsk := by rw [htask]

/-- Under valid dynamic suspensions, the total suspension of the jobs of `tsk` arriving in `[t1, t1 + Δ)`,
within that interval, is at most `max_arrivals tsk Δ` times the task's total suspension bound. -/
theorem suspension_of_task_bounded [MaxArrivals Task] [TaskTotalSuspension Task] [JobTask Job Task]
    [JobArrival Job] [JobCost Job] [JobSuspension Job] :
    valid_dynamic_suspensions (Job := Job) (Task := Task) →
    ∀ (arr_seq : arrival_sequence Job) (PState : ProcessorState Job) (sched : schedule PState) (tsk : Task)
      (t1 : instant) (Δ : duration),
      respects_max_arrivals arr_seq tsk (max_arrivals tsk) →
      ∑ t ∈ Finset.Ico (α := Nat) t1 (t1 + Δ),
          sumSeq (task_arrivals_between arr_seq tsk t1 (t1 + Δ)) (fun j => (suspended sched j t).toNat)
        ≤ max_arrivals tsk Δ * task_total_suspension tsk := by
  intro hvalid arr_seq PState sched tsk t1 Δ hresp
  rw [sum_sumSeq_comm]
  have hbound := sumSeq_le_length_mul (task_arrivals_between arr_seq tsk t1 (t1 + Δ))
    (fun j => ∑ t ∈ Finset.Ico (α := Nat) t1 (t1 + Δ), (suspended sched j t).toNat)
    (task_total_suspension tsk) (fun j hj => by
      have hjt : job_of_task tsk j = true := (List.mem_filter.mp hj).2
      exact job_suspension_bounded hvalid PState sched tsk t1 Δ j hjt)
  have hnum : (task_arrivals_between arr_seq tsk t1 (t1 + Δ)).length ≤ max_arrivals tsk Δ := by
    have := hresp t1 (t1 + Δ) (Nat.le_add_right t1 Δ)
    unfold number_of_task_arrivals at this
    rwa [Nat.add_sub_cancel_left] at this
  exact Nat.le_trans hbound (Nat.mul_le_mul_right _ hnum)

end TotalSuspensionBounded

end Prosa.Analysis.Facts.Model.DynamicSuspension
