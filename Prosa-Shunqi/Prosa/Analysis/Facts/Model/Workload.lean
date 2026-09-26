-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/facts/model/workload.v

import Prosa.Model.Aggregate.Workload
import Prosa.Analysis.Facts.Behavior.Arrivals

namespace Prosa.Analysis.Facts.Model.Workload

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Time
open Prosa.Model.Task.Concept
open Prosa.Model.Priority.Definitions
open Prosa.Model.Aggregate.Workload
open Prosa.Util.Sum
open Prosa.Analysis.Facts.Behavior.Arrivals

/-! Facts about the workload of sets of jobs. Binders follow the elaborated
source types (unused section classes are absent). Representation: a MathComp
`pred T` is `T → Bool`; `predT`/`pred0` are the constant predicates; `x \in xs`
in `Prop` position is `decide (x ∈ xs) = true`; `uniq xs` is `xs.Nodup`;
`{in xs, P}` is `∀ x, decide (x ∈ xs) = true → P x`; `a != b` is
`decide (a ≠ b)`; `a == b` is `decide (a = b)`; `f^~ y` is `fun x => f x y`;
`t1 <= t <= t2` is the Boolean conjunction of decides; a Boolean `if` is
`bif`; `\sum_(x <- xs | Q x) F x` is `sumFiltered xs Q F`. -/

macro "omega'" : tactic => `(tactic| (try dsimp only [instant, duration, work] at *) <;> omega)

private theorem sf_cons {I : Type _} (a : I) (l : List I) (P : I → Bool) (F : I → Nat) :
    sumFiltered (a :: l) P F = (bif P a then F a else 0) + sumFiltered l P F := by
  unfold sumFiltered; cases h : P a <;> simp [List.filter_cons, h]

private theorem arrivals_between_empty {Job : JobType} [DecidableEq Job]
    (arr_seq : arrival_sequence Job) (t1 t2 : Nat) (h : t2 ≤ t1) :
    arrivals_between arr_seq t1 t2 = [] := by
  unfold arrivals_between Prosa.Util.Notation.bigCat
  rw [Nat.sub_eq_zero_of_le h]; rfl

private theorem filter_eq_singleton {Job : JobType} [DecidableEq Job] (j : Job) :
    ∀ l : List Job, l.Nodup → j ∈ l → l.filter (fun x => decide (x = j)) = [j]
  | [], _, hm => absurd hm List.not_mem_nil
  | a :: l, hnd, hm => by
    rw [List.nodup_cons] at hnd
    by_cases he : a = j
    · subst he
      have : l.filter (fun x => decide (x = a)) = [] := by
        rw [List.filter_eq_nil_iff]; intro x hx
        have : x ≠ a := fun e => hnd.1 (e ▸ hx)
        simp [this]
      simp [List.filter_cons, this]
    · have hl : j ∈ l := by
        rcases List.mem_cons.mp hm with e | h
        · exact absurd e.symm he
        · exact h
      simp [List.filter_cons, he, filter_eq_singleton j l hnd.2 hl]

/-- Filtering the job list by a weaker predicate leaves the workload unchanged. -/
theorem workload_of_jobs_filter {Job : JobType} [DecidableEq Job] [JobCost Job]
    (P1 P2 : Job → Bool) (jobs : List Job) :
    (∀ j : Job, decide (j ∈ jobs) = true → P1 j = true → P2 j = true) →
    workload_of_jobs P1 jobs = workload_of_jobs P1 (jobs.filter P2) := by
  intro h
  unfold workload_of_jobs sumFiltered
  rw [List.filter_filter]
  congr 2
  apply List.filter_congr
  intro j hj
  cases hp : P1 j
  · simp
  · simp [h j (decide_eq_true hj) hp]

/-- A weaker predicate has no smaller workload. -/
theorem workload_of_jobs_weaken {Job : JobType} [DecidableEq Job] [JobCost Job]
    (P1 P2 : Job → Bool) (jobs : List Job) :
    (∀ j : Job, P1 j = true → P2 j = true) →
    workload_of_jobs P1 jobs ≤ workload_of_jobs P2 jobs := by
  intro h
  unfold workload_of_jobs
  induction jobs with
  | nil => exact Nat.le_refl _
  | cons a l ih =>
    rw [sf_cons, sf_cons]
    cases h1 : P1 a
    · cases h2 : P2 a <;> simp only [cond_false, cond_true] <;> omega
    · rw [h a h1]; simp only [cond_true]; omega

/-- The empty job list has no workload. -/
theorem workload_of_jobs0 {Job : JobType} [DecidableEq Job] [JobCost Job]
    (P : Job → Bool) : workload_of_jobs P [] = 0 := rfl

/-- Workload bounded by the sum over task partitions. -/
theorem workload_of_jobs_le_sum_over_partitions {Task : TaskType} [DecidableEq Task]
    {Job : JobType} [DecidableEq Job] [JobTask Job Task] [JobCost Job]
    (P : Job → Bool) (Q : Task → Bool) (js : List Job) (ts : List Task) :
    (∀ j : Job, decide (j ∈ js) = true → decide (job_task j ∈ ts) = true) →
    (∀ j : Job, decide (j ∈ js) = true → P j = true → Q (job_task j) = true) →
    let P_and_job_of := fun (tsk_o : Task) (j : Job) => P j && decide (job_task j = tsk_o)
    workload_of_jobs P js ≤
      sumFiltered ts Q (fun tsk_o => workload_of_jobs (P_and_job_of tsk_o) js) := by
  intro hin hPQ P_and_job_of
  show sumFiltered js P (fun j => job_cost j) ≤
    sumOverPartitions (fun j => job_task j) (fun j => job_cost j) P js (ts.filter Q)
  apply sum_over_partitions_le
  intro x hx hPx
  rw [List.mem_filter]
  exact ⟨of_decide_eq_true (hin x (decide_eq_true hx)), hPQ x (decide_eq_true hx) hPx⟩

/-- With unique jobs and tasks, the workload is the sum over task partitions. -/
theorem workload_of_jobs_partitioned_by_tasks {Task : TaskType} [DecidableEq Task]
    {Job : JobType} [DecidableEq Job] [JobTask Job Task] [JobCost Job]
    (P : Job → Bool) (Q : Task → Bool) (js : List Job) (ts : List Task) :
    (∀ j : Job, decide (j ∈ js) = true → decide (job_task j ∈ ts) = true) →
    (∀ j : Job, decide (j ∈ js) = true → P j = true → Q (job_task j) = true) →
    js.Nodup → ts.Nodup →
    let P_and_job_of := fun (tsk_o : Task) (j : Job) => P j && decide (job_task j = tsk_o)
    workload_of_jobs P js =
      sumFiltered ts Q (fun tsk_o => workload_of_jobs (P_and_job_of tsk_o) js) := by
  intro hin hPQ hjs hts P_and_job_of
  show sumFiltered js P (fun j => job_cost j) =
    sumOverPartitions (fun j => job_task j) (fun j => job_cost j) P js (ts.filter Q)
  apply sum_over_partitions_eq
  · intro x hx hPx
    rw [List.mem_filter]
    exact ⟨of_decide_eq_true (hin x (decide_eq_true hx)), hPQ x (decide_eq_true hx) hPx⟩
  · exact hjs
  · exact hts.filter Q

/-- Splitting the other higher-or-equal-priority workload by task. -/
theorem workload_of_other_jobs_split {Task : TaskType} [DecidableEq Task]
    {Job : JobType} [DecidableEq Job] [JobTask Job Task] [JobCost Job] [JLFP_policy Job]
    (jobs : List Job) (j : Job) :
    workload_of_jobs (fun x => another_hep_job x j) jobs =
      workload_of_jobs (fun x => another_task_hep_job (Task := Task) x j) jobs +
        workload_of_jobs (fun x => another_hep_job_of_same_task (Task := Task) x j) jobs := by
  unfold workload_of_jobs
  apply sum_split_exhaustive_mutually_exclusive_preds
  · intro x
    unfold another_hep_job another_task_hep_job another_hep_job_of_same_task another_hep_job
    cases hep_job x j <;> by_cases hx : x = j <;>
      by_cases ht : job_task (Task := Task) x = job_task (Task := Task) j <;> simp [hx, ht]
  · intro x
    unfold another_task_hep_job another_hep_job_of_same_task another_hep_job
    by_cases ht : job_task (Task := Task) x = job_task (Task := Task) j <;> simp [ht]

/-- The empty predicate has no workload. -/
theorem workload_of_jobs_pred0 {Job : JobType} [DecidableEq Job] [JobCost Job]
    (jobs : List Job) : workload_of_jobs (fun _ => false) jobs = 0 := by
  unfold workload_of_jobs sumFiltered
  simp

/-- Case analysis of the workload on a second predicate. -/
theorem workload_of_jobs_case_on_pred {Job : JobType} [DecidableEq Job] [JobCost Job]
    (jobs : List Job) (P P' : Job → Bool) :
    workload_of_jobs P jobs =
      workload_of_jobs (fun j => P j && P' j) jobs +
        workload_of_jobs (fun j => P j && !P' j) jobs := by
  unfold workload_of_jobs
  apply sum_split_exhaustive_mutually_exclusive_preds
  · intro x; cases P x <;> cases P' x <;> rfl
  · intro x; cases P x <;> cases P' x <;> rfl

/-- Predicates agreeing on the job list give the same workload. -/
theorem workload_of_jobs_equiv_pred {Job : JobType} [DecidableEq Job] [JobCost Job]
    (jobs : List Job) (P P' : Job → Bool) :
    (∀ j : Job, decide (j ∈ jobs) = true → P j = P' j) →
    workload_of_jobs P jobs = workload_of_jobs P' jobs := by
  intro h
  unfold workload_of_jobs sumFiltered
  congr 2
  apply List.filter_congr
  intro j hj
  exact h j (decide_eq_true hj)

/-- The workload of an arrived job is its cost when it arrives in the interval. -/
theorem workload_of_job_eq_job_arrival {Job : JobType} [DecidableEq Job] [JobArrival Job]
    [JobCost Job] (arr_seq : arrival_sequence Job) :
    consistent_arrival_times arr_seq → arrival_sequence_uniq arr_seq →
    ∀ (j : Job) (t1 t2 : instant), arrives_in arr_seq j →
      workload_of_job arr_seq j t1 t2 =
        bif decide (t1 ≤ job_arrival j) && decide (job_arrival j < t2) then job_cost j else 0 := by
  intro hc hu j t1 t2 harr
  have hnd : (arrivals_between arr_seq t1 t2).Nodup := arrivals_uniq arr_seq hc hu t1 t2
  unfold workload_of_job workload_of_jobs sumFiltered
  cases hb : (decide (t1 ≤ job_arrival j) && decide (job_arrival j < t2))
  · have hnot : j ∉ arrivals_between arr_seq t1 t2 := by
      intro hm
      have h1 := job_arrival_between_ge arr_seq hc j t1 t2 (decide_eq_true hm)
      have h2 := job_arrival_between_lt arr_seq hc j t1 t2 (decide_eq_true hm)
      simp [h1, h2] at hb
    have : (arrivals_between arr_seq t1 t2).filter (fun x => decide (x = j)) = [] := by
      rw [List.filter_eq_nil_iff]; intro x hx; simp only [decide_eq_true_eq]
      intro e; subst e; exact hnot hx
    rw [this]; rfl
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
    have hm : j ∈ arrivals_between arr_seq t1 t2 :=
      of_decide_eq_true (job_in_arrivals_between arr_seq hc j t1 t2 harr hb.1 hb.2)
    have : (arrivals_between arr_seq t1 t2).filter (fun x => decide (x = j)) = [j] := by
      exact filter_eq_singleton j _ hnd hm
    rw [this]; simp

/-- The workload of a job plus the other higher-or-equal-priority workload is the
higher-or-equal-priority workload. -/
theorem workload_job_and_ahep_eq_workload_hep {Job : JobType} [DecidableEq Job] [JobCost Job]
    (arr_seq : arrival_sequence Job) (JLFP : JLFP_policy Job) :
    reflexive_job_priorities JLFP →
    ∀ (j : Job) (t1 t2 : instant),
      workload_of_job arr_seq j t1 t2 + workload_of_other_hep_jobs arr_seq j t1 t2 =
        workload_of_hep_jobs arr_seq j t1 t2 := by
  intro hrefl j t1 t2
  unfold workload_of_job workload_of_other_hep_jobs workload_of_hep_jobs workload_of_jobs
  symm
  apply sum_split_exhaustive_mutually_exclusive_preds
  · intro x
    unfold another_hep_job
    by_cases hx : x = j
    · subst hx; simp [hrefl x]
    · simp [hx]
  · intro x
    unfold another_hep_job
    by_cases hx : x = j <;> simp [hx]

/-- Jobs arriving after `t` that do not satisfy `P` can be cut from the interval. -/
theorem workload_of_jobs_nil_tail {Job : JobType} [DecidableEq Job] [JobArrival Job]
    [JobCost Job] (arr_seq : arrival_sequence Job) :
    consistent_arrival_times arr_seq →
    ∀ (P : Job → Bool) (t1 : instant) (t2 t : Nat), t ≤ t2 →
      (∀ j : Job, decide (j ∈ arrivals_between arr_seq t1 t2) = true →
        t ≤ job_arrival j → (!P j) = true) →
      workload_of_jobs P (arrivals_between arr_seq t1 t2) =
        workload_of_jobs P (arrivals_between arr_seq t1 t) := by
  intro hc P t1 t2 t hle h
  by_cases h1 : t1 ≤ t
  · rw [arrivals_between_cat arr_seq t1 t t2 h1 hle]
    unfold workload_of_jobs sumFiltered
    rw [List.filter_append]
    have : (arrivals_between arr_seq t t2).filter P = [] := by
      rw [List.filter_eq_nil_iff]; intro x hx
      have hm : decide (x ∈ arrivals_between arr_seq t1 t2) = true := by
        rw [arrivals_between_cat arr_seq t1 t t2 h1 hle]; simp [hx]
      have hge := job_arrival_between_ge arr_seq hc x t t2 (decide_eq_true hx)
      have := h x hm hge
      simpa using this
    rw [this]; simp
  · have hnil : arrivals_between arr_seq t1 t = [] := by
      exact arrivals_between_empty arr_seq t1 t (by omega')
    rw [hnil]
    unfold workload_of_jobs sumFiltered
    have : (arrivals_between arr_seq t1 t2).filter P = [] := by
      rw [List.filter_eq_nil_iff]; intro x hx
      have hge := job_arrival_between_ge arr_seq hc x t1 t2 (decide_eq_true hx)
      have := h x (decide_eq_true hx) (by omega')
      simpa using this
    rw [this]; rfl

/-- The workload over `[t1, t2)` splits at any intermediate `t`. -/
theorem workload_of_jobs_cat {Job : JobType} [DecidableEq Job] [JobCost Job]
    (arr_seq : arrival_sequence Job) (t t1 t2 : Nat) (P : Job → Bool) :
    (decide (t1 ≤ t) && decide (t ≤ t2)) = true →
    workload_of_jobs P (arrivals_between arr_seq t1 t2) =
      workload_of_jobs P (arrivals_between arr_seq t1 t) +
        workload_of_jobs P (arrivals_between arr_seq t t2) := by
  intro h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  rw [arrivals_between_cat arr_seq t1 t t2 h.1 h.2]
  unfold workload_of_jobs sumFiltered
  rw [List.filter_append, List.map_append, List.sum_append]

/-- The workload is monotone in the interval end. -/
theorem workload_of_jobs_reduce_range {Job : JobType} [DecidableEq Job] [JobCost Job]
    (arr_seq : arrival_sequence Job) (t1 t2 t3 : Nat) (P : Job → Bool) :
    t1 ≤ t2 → t2 ≤ t3 →
    workload_of_jobs P (arrivals_between arr_seq t1 t2) ≤
      workload_of_jobs P (arrivals_between arr_seq t1 t3) := by
  intro h12 h23
  rw [workload_of_jobs_cat arr_seq t2 t1 t3 P (by simp [h12, h23])]
  exact Nat.le_add_right _ _

/-- Removing a member job subtracts its cost when it satisfies the predicate. -/
theorem workload_minus_job_cost' {Job : JobType} [DecidableEq Job] [JobCost Job]
    (j : Job) (jobs : List Job) :
    jobs.Nodup → decide (j ∈ jobs) = true →
    ∀ P : Job → Bool,
      workload_of_jobs (fun jhp => P jhp && decide (jhp ≠ j)) jobs =
        workload_of_jobs P jobs - (bif P j then job_cost j else 0) := by
  intro hnd hin P
  have hin' := of_decide_eq_true hin
  unfold workload_of_jobs
  induction jobs with
  | nil => exact absurd hin' List.not_mem_nil
  | cons a l ih =>
    rw [List.nodup_cons] at hnd
    rw [sf_cons, sf_cons]
    by_cases he : a = j
    · subst he
      have hl : sumFiltered l (fun jhp => P jhp && decide (jhp ≠ a)) (fun j => job_cost j) =
          sumFiltered l P (fun j => job_cost j) := by
        unfold sumFiltered; congr 2; apply List.filter_congr; intro x hx
        have : x ≠ a := fun e => hnd.1 (e ▸ hx)
        simp [this]
      rw [hl]
      cases hp : P a <;> simp only [ne_eq, not_true_eq_false, decide_false, Bool.and_false,
        cond_true, cond_false] <;> omega
    · have hl : j ∈ l := by
        rcases List.mem_cons.mp hin' with e | h
        · exact absurd e.symm he
        · exact h
      have ih' := ih hnd.2 (decide_eq_true hl) hl
      have hle : (bif P j then job_cost j else 0) ≤ sumFiltered l P (fun j => job_cost j) := by
        cases hp : P j
        · exact Nat.zero_le _
        · have : j ∈ l.filter P := List.mem_filter.mpr ⟨hl, hp⟩
          exact List.le_sum_of_mem (List.mem_map_of_mem this)
      simp only [ne_eq] at ih' ⊢
      cases hpa : P a <;>
        simp only [he, not_false_eq_true, decide_true, Bool.and_true,
          cond_true, cond_false] <;> omega'

/-- Removing a member job subtracts its cost. -/
theorem workload_minus_job_cost {Job : JobType} [DecidableEq Job] [JobCost Job]
    (j : Job) (jobs : List Job) :
    jobs.Nodup → decide (j ∈ jobs) = true →
    workload_of_jobs (fun jhp => decide (jhp ≠ j)) jobs =
      workload_of_jobs (fun _ => true) jobs - job_cost j := by
  intro hnd hin
  have := workload_minus_job_cost' j jobs hnd hin (fun _ => true)
  simpa using this

/-- Restricting to jobs arriving by `t` bounds the workload by the workload up to `t`. -/
theorem workload_equal_subset {Job : JobType} [DecidableEq Job] [JobArrival Job] [JobCost Job]
    (arr_seq : arrival_sequence Job) :
    consistent_arrival_times arr_seq → valid_arrival_sequence arr_seq →
    ∀ (t1 t2 t : instant) (P : Job → Bool),
      workload_of_jobs (fun j => decide (job_arrival j ≤ t) && P j) (arrivals_between arr_seq t1 t2) ≤
        workload_of_jobs (fun x => P x) (arrivals_between arr_seq t1 (t + 1)) := by
  intro hc hva t1 t2 t P
  by_cases h : t2 ≤ t + 1
  · calc workload_of_jobs (fun j => decide (job_arrival j ≤ t) && P j) (arrivals_between arr_seq t1 t2)
        ≤ workload_of_jobs (fun x => P x) (arrivals_between arr_seq t1 t2) :=
          workload_of_jobs_weaken _ _ _ (fun j hj => by simp at hj; simp [hj.2])
      _ ≤ workload_of_jobs (fun x => P x) (arrivals_between arr_seq t1 (t + 1)) := by
          by_cases h1 : t1 ≤ t2
          · exact workload_of_jobs_reduce_range arr_seq t1 t2 (t + 1) _ h1 h
          · have hnil : arrivals_between arr_seq t1 t2 = [] := by
              exact arrivals_between_empty arr_seq _ _ (by omega')
            rw [hnil]; exact Nat.zero_le _
  · have hsplit : workload_of_jobs (fun j => decide (job_arrival j ≤ t) && P j)
        (arrivals_between arr_seq t1 t2) =
        workload_of_jobs (fun j => decide (job_arrival j ≤ t) && P j)
          (arrivals_between arr_seq t1 (t + 1)) := by
      apply workload_of_jobs_nil_tail arr_seq hc _ t1 t2 (t + 1) (by omega')
      intro j _ hge
      have : ¬ job_arrival j ≤ t := by omega'
      simp [this]
    rw [hsplit]
    exact workload_of_jobs_weaken _ _ _ (fun j hj => by simp at hj; simp [hj.2])

end Prosa.Analysis.Facts.Model.Workload
