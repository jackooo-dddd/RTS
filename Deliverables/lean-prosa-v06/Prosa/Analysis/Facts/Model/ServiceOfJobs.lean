-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/facts/model/service_of_jobs.v

import Prosa.Model.Aggregate.Workload
import Prosa.Model.Aggregate.ServiceOfJobs
import Prosa.Analysis.Facts.Behavior.Completion
import Prosa.Analysis.Facts.BusyInterval.QuietTime
import Prosa.Analysis.Facts.Model.Uniprocessor

namespace Prosa.Analysis.Facts.Model.ServiceOfJobs

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Ready
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Behavior.Time
open Prosa.Model.Priority.Definitions
open Prosa.Model.Processor.PlatformProperties
open Prosa.Model.Aggregate.Workload
open Prosa.Model.Aggregate.ServiceOfJobs
open Prosa.Util.Sum
open Prosa.Analysis.Definitions.Service
open Prosa.Analysis.Definitions.BusyInterval.Classical
open Prosa.Analysis.Facts.Behavior.Arrivals
open Prosa.Analysis.Facts.Behavior.Service
open Prosa.Analysis.Facts.Behavior.Completion
open scoped BigOperators

/-! Lemmas about the service received by sets of jobs. Binders follow the
elaborated source types (unused section classes and hypotheses are absent).
Representation: a MathComp `pred Job` is `Job → Bool`; `pred0` is
`fun _ => false`; `x \in xs` in `Prop` position is `decide (x ∈ xs) = true`;
`uniq xs` is `xs.Nodup`; `{in xs, P1 =1 P2}` is
`∀ x, decide (x ∈ xs) = true → P1 x = P2 x`; `t1 <= t <= t2` and
`t1 <= t < t2` are Boolean conjunctions of decides; a single comparison in
`Prop` position is the Lean proposition; `~~ b` is `!b`; `has P xs` is
`xs.any P`; `\sum_(t1 <= t < t2) F t` is `∑ t ∈ (Finset.Ico t1 t2 : Finset Nat), F t` (the
MathComp index is `nat`), with a Boolean summand coerced by `Bool.toNat`; `t.+1` is `t + 1`. -/

macro "omega'" : tactic => `(tactic| (try dsimp only [instant, duration, work] at *) <;> omega)

private theorem sf_cons {I : Type _} (a : I) (l : List I) (P : I → Bool) (F : I → Nat) :
    sumFiltered (a :: l) P F = (bif P a then F a else 0) + sumFiltered l P F := by
  unfold sumFiltered; cases h : P a <;> simp [h]

private theorem sf_nil {I : Type _} (P : I → Bool) (F : I → Nat) :
    sumFiltered [] P F = 0 := by
  simp [sumFiltered]

private theorem sf_append {I : Type _} (L1 L2 : List I) (P : I → Bool) (F : I → Nat) :
    sumFiltered (L1 ++ L2) P F = sumFiltered L1 P F + sumFiltered L2 P F := by
  unfold sumFiltered; simp [List.filter_append]

private theorem sf_congr {I : Type _} (L : List I) (P : I → Bool) (F G : I → Nat)
    (h : ∀ x, x ∈ L → P x = true → F x = G x) :
    sumFiltered L P F = sumFiltered L P G := by
  unfold sumFiltered
  congr 1
  apply List.map_congr_left
  intro x hx
  rw [List.mem_filter] at hx
  exact h x hx.1 hx.2

private theorem sf_add {I : Type _} (L : List I) (P : I → Bool) (F G : I → Nat) :
    sumFiltered L P (fun x => F x + G x) = sumFiltered L P F + sumFiltered L P G := by
  induction L with
  | nil => simp [sf_nil]
  | cons a L ih =>
    rw [sf_cons, sf_cons, sf_cons, ih]
    cases P a <;> simp only [cond_true, cond_false] <;> omega

private theorem sf_le {I : Type _} (L : List I) (P : I → Bool) (F G : I → Nat)
    (h : ∀ x, x ∈ L → P x = true → F x ≤ G x) :
    sumFiltered L P F ≤ sumFiltered L P G := by
  induction L with
  | nil => simp [sf_nil]
  | cons a L ih =>
    rw [sf_cons, sf_cons]
    have hr := ih (fun x hx hp => h x (List.mem_cons_of_mem a hx) hp)
    cases hp : P a
    · simp only [cond_false]; omega
    · have := h a List.mem_cons_self hp
      simp only [cond_true]; omega

private theorem sf_zero {I : Type _} (L : List I) (P : I → Bool) (F : I → Nat)
    (h : ∀ x, x ∈ L → P x = true → F x = 0) : sumFiltered L P F = 0 := by
  induction L with
  | nil => exact sf_nil P F
  | cons a L ih =>
    rw [sf_cons, ih (fun x hx hp => h x (List.mem_cons_of_mem a hx) hp)]
    cases hp : P a
    · rfl
    · simp [h a List.mem_cons_self hp]

private theorem sf_exchange {I : Type _} (L : List I) (P : I → Bool) (f : I → Nat → Nat)
    (t1 t2 : Nat) :
    sumFiltered L P (fun j => ∑ t ∈ Finset.Ico t1 t2, f j t) =
      ∑ t ∈ Finset.Ico t1 t2, sumFiltered L P (fun j => f j t) := by
  induction L with
  | nil => simp [sf_nil]
  | cons a L ih =>
    simp only [sf_cons, ih]
    cases P a
    · simp
    · simp only [cond_true, Finset.sum_add_distrib]

private theorem service_during_empty {Job : JobType} [DecidableEq Job]
    {PState : ProcessorState Job} (sched : schedule PState) (j : Job) (t1 t2 : Nat)
    (h : t2 ≤ t1) : service_during sched j t1 t2 = 0 := by
  unfold service_during
  simp [Finset.Ico_eq_empty_of_le h]

/-- The total service of the jobs arriving in `[t1, t2)` splits at `t`. -/
theorem service_of_jobs_cat_scheduling_interval {Job : JobType} [DecidableEq Job]
    [JobArrival Job] {PState : ProcessorState Job} (arr_seq : arrival_sequence Job) :
    consistent_arrival_times arr_seq →
    ∀ sched : schedule PState, jobs_must_arrive_to_execute sched →
    ∀ (P : Job → Bool) (t1 t2 t : Nat), (decide (t1 ≤ t) && decide (t ≤ t2)) = true →
      service_of_jobs sched P (arrivals_between arr_seq t1 t2) t1 t2 =
        service_of_jobs sched P (arrivals_between arr_seq t1 t) t1 t +
          service_of_jobs sched P (arrivals_between arr_seq t1 t) t t2 +
          service_of_jobs sched P (arrivals_between arr_seq t t2) t t2 := by
  intro hc sched hmust P t1 t2 t h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h1, h2⟩ := h
  rw [arrivals_between_cat arr_seq t1 t t2 h1 h2]
  unfold service_of_jobs
  rw [sf_append]
  have hA : sumFiltered (arrivals_between arr_seq t1 t) P
        (fun j => service_during sched j t1 t2) =
      sumFiltered (arrivals_between arr_seq t1 t) P (fun j => service_during sched j t1 t) +
        sumFiltered (arrivals_between arr_seq t1 t) P (fun j => service_during sched j t t2) := by
    rw [← sf_add]
    apply sf_congr; intro x _ _
    exact (service_during_cat sched x t1 t t2 (by simp [h1, h2])).symm
  have hB : sumFiltered (arrivals_between arr_seq t t2) P
        (fun j => service_during sched j t1 t2) =
      sumFiltered (arrivals_between arr_seq t t2) P (fun j => service_during sched j t t2) := by
    apply sf_congr; intro x hx _
    rw [← service_during_cat sched x t1 t t2 (by simp [h1, h2])]
    have hge := job_arrival_between_ge arr_seq hc x t t2 (decide_eq_true hx)
    rw [cumulative_service_before_job_arrival_zero sched x hmust t1 t hge, Nat.zero_add]
  rw [hA, hB]

/-- The service during `[t, t2)` of the jobs arriving in `[t1, t2)` splits by
arrival at `t`. -/
theorem service_of_jobs_cat_arrival_interval {Job : JobType} [DecidableEq Job]
    {PState : ProcessorState Job} (arr_seq : arrival_sequence Job) (sched : schedule PState)
    (P : Job → Bool) (t1 t2 t : Nat) :
    (decide (t1 ≤ t) && decide (t ≤ t2)) = true →
      service_of_jobs sched P (arrivals_between arr_seq t1 t2) t t2 =
        service_of_jobs sched P (arrivals_between arr_seq t1 t) t t2 +
          service_of_jobs sched P (arrivals_between arr_seq t t2) t t2 := by
  intro h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  rw [arrivals_between_cat arr_seq t1 t t2 h.1 h.2]
  unfold service_of_jobs
  exact sf_append _ _ _ _

/-- Case analysis of the service on a second predicate. -/
theorem service_of_jobs_case_on_pred {Job : JobType} [DecidableEq Job]
    {PState : ProcessorState Job} (sched : schedule PState) (jobs : List Job)
    (t1 t2 : instant) (P1 P2 : Job → Bool) :
    service_of_jobs sched P1 jobs t1 t2 =
      service_of_jobs sched (fun j => P1 j && P2 j) jobs t1 t2 +
        service_of_jobs sched (fun j => P1 j && !P2 j) jobs t1 t2 := by
  unfold service_of_jobs
  apply sum_split_exhaustive_mutually_exclusive_preds
  · intro x; cases P1 x <;> cases P2 x <;> rfl
  · intro x; cases P1 x <;> cases P2 x <;> rfl

/-- The service of the jobs satisfying `P` is the total service minus the
service of the jobs not satisfying `P`. -/
theorem service_of_jobs_negate_pred {Job : JobType} [DecidableEq Job]
    {PState : ProcessorState Job} (sched : schedule PState) (P : Job → Bool)
    (jobs : List Job) (t1 t2 : instant) :
    service_of_jobs sched P jobs t1 t2 =
      total_service_of_jobs_in sched jobs t1 t2 -
        service_of_jobs sched (fun j => !P j) jobs t1 t2 := by
  unfold total_service_of_jobs_in service_of_jobs
  have := sum_split_exhaustive_mutually_exclusive_preds jobs (fun _ => true)
    (fun j => service_during sched j t1 t2) P (fun j => !P j)
    (fun x => by cases P x <;> rfl) (fun x => by cases P x <;> rfl)
  omega

/-- The service is monotone in the predicate. -/
theorem service_of_jobs_pred_impl {Job : JobType} [DecidableEq Job]
    {PState : ProcessorState Job} (sched : schedule PState) (jobs : List Job)
    (t1 t2 : instant) (P1 P2 : Job → Bool) :
    (∀ j : Job, decide (j ∈ jobs) = true → P1 j = true → P2 j = true) →
      service_of_jobs sched P1 jobs t1 t2 ≤ service_of_jobs sched P2 jobs t1 t2 := by
  intro h
  exact leq_sum_seq_pred jobs _ P1 P2 (fun i hi hp => h i (decide_eq_true hi) hp)

/-- Predicates agreeing on the job list give the same service. -/
theorem service_of_jobs_equiv_pred {Job : JobType} [DecidableEq Job]
    {PState : ProcessorState Job} (sched : schedule PState) (jobs : List Job)
    (t1 t2 : instant) (P1 P2 : Job → Bool) :
    (∀ j : Job, decide (j ∈ jobs) = true → P1 j = P2 j) →
      service_of_jobs sched P1 jobs t1 t2 = service_of_jobs sched P2 jobs t1 t2 := by
  intro h
  unfold service_of_jobs sumFiltered
  congr 2
  apply List.filter_congr
  intro j hj
  exact h j (decide_eq_true hj)

/-- The service over an interval is the sum of the per-instant services. -/
theorem service_of_jobs_sum_over_time_interval {Job : JobType} [DecidableEq Job]
    {PState : ProcessorState Job} (sched : schedule PState) (P : Job → Bool)
    (jobs : List Job) (t1 t2 : instant) :
    service_of_jobs sched P jobs t1 t2 =
      ∑ t ∈ (Finset.Ico t1 t2 : Finset Nat), service_of_jobs_at sched P jobs t := by
  unfold service_of_jobs service_of_jobs_at service_during
  exact sf_exchange jobs P (fun j t => service_at sched j t) t1 t2

/-- The service of no jobs is zero. -/
theorem service_of_jobs_pred0 {Job : JobType} [DecidableEq Job]
    {PState : ProcessorState Job} (sched : schedule PState) (jobs : List Job)
    (t1 t2 : instant) :
    service_of_jobs sched (fun _ => false) jobs t1 t2 = 0 := by
  unfold service_of_jobs
  simp [sumFiltered]

/-- If no job of `jobs` is both scheduled at `t` and satisfies `P`, the
service at `t` is zero. -/
theorem service_of_jobs_nsched_or_unsat {Job : JobType} [DecidableEq Job]
    {PState : ProcessorState Job} (sched : schedule PState) (P : Job → Bool)
    (jobs : List Job) (t : instant) :
    (∀ j : Job, decide (j ∈ jobs) = true → (!(P j && scheduled_at sched j t)) = true) →
      service_of_jobs_at sched P jobs t = 0 := by
  intro h
  unfold service_of_jobs_at
  apply sf_zero
  intro x hx hp
  have hx' := h x (decide_eq_true hx)
  rw [hp, Bool.true_and] at hx'
  exact not_scheduled_implies_no_service sched x t hx'

/-- The service in an empty interval is zero. -/
theorem service_of_jobs_geq {Job : JobType} [DecidableEq Job]
    {PState : ProcessorState Job} (sched : schedule PState) (P : Job → Bool)
    (jobs : List Job) (t1 t2 : instant) :
    t2 ≤ t1 → service_of_jobs sched P jobs t1 t2 = 0 := by
  intro h
  unfold service_of_jobs
  exact sf_zero _ _ _ (fun x _ _ => service_during_empty sched x t1 t2 h)

/-- The service in `[t1, t2]` is the service in `[t1, t2)` plus the service at `t2`. -/
theorem service_of_jobs_cat_last {Job : JobType} [DecidableEq Job]
    {PState : ProcessorState Job} (sched : schedule PState) (P : Job → Bool)
    (js : List Job) (t1 t2 : Nat) :
    t1 ≤ t2 →
      service_of_jobs sched P js t1 (t2 + 1) =
        service_of_jobs sched P js t1 t2 + service_of_jobs_at sched P js t2 := by
  intro h
  rw [service_of_jobs_sum_over_time_interval, service_of_jobs_sum_over_time_interval]
  exact Finset.sum_Ico_succ_top h _

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
      simp [this]
    · have hl : j ∈ l := by
        rcases List.mem_cons.mp hm with e | h
        · exact absurd e.symm he
        · exact h
      simp [he, filter_eq_singleton j l hnd.2 hl]

/-- The service of `j` plus the service of the other higher-or-equal-priority
jobs is the service of the higher-or-equal-priority jobs. -/
theorem service_plus_ahep_eq_service_hep {Job : JobType} [DecidableEq Job]
    [JobArrival Job] {PState : ProcessorState Job} (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    ∀ sched : schedule PState, jobs_must_arrive_to_execute sched →
    ∀ JLFP : JLFP_policy Job, reflexive_job_priorities JLFP →
    ∀ (t1 t2 : instant) (j : Job), arrives_in arr_seq j → t1 ≤ job_arrival j →
      service_during sched j t1 t2 + service_of_other_hep_jobs arr_seq sched j t1 t2 =
        service_of_hep_jobs arr_seq sched j t1 t2 := by
  intro hvalid sched hmust JLFP hrefl t1 t2 j harr hle
  obtain ⟨hc, hu⟩ := hvalid
  unfold service_of_other_hep_jobs service_of_hep_jobs service_of_jobs
  have hsplit := sum_split_exhaustive_mutually_exclusive_preds
    (arrivals_between arr_seq t1 t2) (fun jhp => hep_job jhp j)
    (fun x => service_during sched x t1 t2) (fun x => decide (x = j))
    (fun jhp => another_hep_job jhp j)
    (fun x => by
      unfold another_hep_job
      by_cases hx : x = j
      · subst hx; simp [hrefl x]
      · simp [hx])
    (fun x => by
      unfold another_hep_job
      by_cases hx : x = j <;> simp [hx])
  rw [hsplit]
  have hself : sumFiltered (arrivals_between arr_seq t1 t2) (fun x => decide (x = j))
      (fun x => service_during sched x t1 t2) = service_during sched j t1 t2 := by
    by_cases hlt : job_arrival j < t2
    · have hm : j ∈ arrivals_between arr_seq t1 t2 :=
        of_decide_eq_true (job_in_arrivals_between arr_seq hc j t1 t2 harr hle hlt)
      unfold sumFiltered
      rw [filter_eq_singleton j _ (arrivals_uniq arr_seq hc hu t1 t2) hm]
      simp
    · have hz := cumulative_service_before_job_arrival_zero sched j hmust t1 t2 (by omega')
      rw [hz]
      apply sf_zero
      intro x _ hx
      rw [of_decide_eq_true hx]
      exact hz
  rw [hself]

/-- The service of a set of jobs is bounded by its workload. -/
theorem service_of_jobs_le_workload {Job : JobType} [DecidableEq Job] [JobCost Job]
    {PState : ProcessorState Job} :
    unit_service_proc_model PState →
    ∀ sched : schedule PState, completed_jobs_dont_execute sched →
    ∀ (P : Job → Bool) (jobs : List Job) (t1 t2 : instant),
      service_of_jobs sched P jobs t1 t2 ≤ workload_of_jobs P jobs := by
  intro hu sched hcd P jobs t1 t2
  unfold service_of_jobs workload_of_jobs
  exact sf_le _ _ _ _ (fun x _ _ => cumulative_service_le_job_cost sched hcd x hu t1 t2)

/-- If the workload equals the service, every job of the interval has completed. -/
theorem workload_eq_service_impl_all_jobs_have_completed {Job : JobType} [DecidableEq Job]
    [JobArrival Job] [JobCost Job] {PState : ProcessorState Job} :
    unit_service_proc_model PState →
    ∀ arr_seq : arrival_sequence Job, consistent_arrival_times arr_seq →
    ∀ sched : schedule PState, jobs_must_arrive_to_execute sched →
      completed_jobs_dont_execute sched →
    ∀ (P : Job → Bool) (t1 t2 t_compl : instant),
      workload_of_jobs P (arrivals_between arr_seq t1 t2) =
          service_of_jobs sched P (arrivals_between arr_seq t1 t2) t1 t_compl →
        ∀ j : Job, decide (j ∈ arrivals_between arr_seq t1 t2) = true → P j = true →
          completed_by sched j t_compl = true := by
  intro hu arr_seq hc sched hmust hcd P t1 t2 t_compl heq j hj hPj
  unfold workload_of_jobs service_of_jobs at heq
  have hall := eq_sum_leq_seq (arrivals_between arr_seq t1 t2) P
    (fun x => service_during sched x t1 t_compl) (fun x => job_cost x)
    (fun x _ _ => cumulative_service_le_job_cost sched hcd x hu t1 t_compl)
  rw [decide_eq_true heq.symm] at hall
  have hj' := List.all_eq_true.mp hall.symm j (of_decide_eq_true hj)
  rw [hPj] at hj'
  simp only [Bool.not_true, Bool.false_or, decide_eq_true_eq] at hj'
  unfold completed_by service
  apply decide_eq_true
  by_cases hlt : t1 ≤ t_compl
  · rw [← service_during_cat sched j 0 t1 t_compl (by simp [hlt]),
      cumulative_service_before_job_arrival_zero sched j hmust 0 t1
        (job_arrival_between_ge arr_seq hc j t1 t2 hj)]
    omega'
  · have := service_during_empty sched j t1 t_compl (by omega')
    omega'

/-- If every job of the interval has completed, the workload equals the service. -/
theorem all_jobs_have_completed_impl_workload_eq_service {Job : JobType} [DecidableEq Job]
    [JobArrival Job] [JobCost Job] {PState : ProcessorState Job} :
    unit_service_proc_model PState →
    ∀ arr_seq : arrival_sequence Job, consistent_arrival_times arr_seq →
    ∀ sched : schedule PState, jobs_must_arrive_to_execute sched →
      completed_jobs_dont_execute sched →
    ∀ (P : Job → Bool) (t1 t2 t_compl : instant),
      (∀ j : Job, decide (j ∈ arrivals_between arr_seq t1 t2) = true → P j = true →
          completed_by sched j t_compl = true) →
        workload_of_jobs P (arrivals_between arr_seq t1 t2) =
          service_of_jobs sched P (arrivals_between arr_seq t1 t2) t1 t_compl := by
  intro hu arr_seq hc sched hmust hcd P t1 t2 t_compl hcompl
  apply Nat.le_antisymm _ (service_of_jobs_le_workload hu sched hcd P _ t1 t_compl)
  unfold workload_of_jobs service_of_jobs
  apply sf_le
  intro x hx hPx
  have hcx := hcompl x (decide_eq_true hx) hPx
  unfold completed_by service at hcx
  have hcx' := of_decide_eq_true hcx
  have hge := job_arrival_between_ge arr_seq hc x t1 t2 (decide_eq_true hx)
  by_cases hlt : t1 ≤ t_compl
  · rw [← service_during_cat sched x 0 t1 t_compl (by simp [hlt]),
      cumulative_service_before_job_arrival_zero sched x hmust 0 t1 hge] at hcx'
    omega'
  · rw [cumulative_service_before_job_arrival_zero sched x hmust 0 t_compl (by omega')] at hcx'
    omega'

/-- All jobs of the interval have completed iff the workload equals the service. -/
theorem all_jobs_have_completed_equiv_workload_eq_service {Job : JobType} [DecidableEq Job]
    [JobArrival Job] [JobCost Job] {PState : ProcessorState Job} :
    unit_service_proc_model PState →
    ∀ arr_seq : arrival_sequence Job, consistent_arrival_times arr_seq →
    ∀ sched : schedule PState, jobs_must_arrive_to_execute sched →
      completed_jobs_dont_execute sched →
    ∀ (P : Job → Bool) (t1 t2 t_compl : instant),
      (∀ j : Job, decide (j ∈ arrivals_between arr_seq t1 t2) = true → P j = true →
          completed_by sched j t_compl = true) ↔
        workload_of_jobs P (arrivals_between arr_seq t1 t2) =
          service_of_jobs sched P (arrivals_between arr_seq t1 t2) t1 t_compl := by
  intro hu arr_seq hc sched hmust hcd P t1 t2 t_compl
  exact ⟨all_jobs_have_completed_impl_workload_eq_service hu arr_seq hc sched hmust hcd
      P t1 t2 t_compl,
    workload_eq_service_impl_all_jobs_have_completed hu arr_seq hc sched hmust hcd
      P t1 t2 t_compl⟩

/-- On a unit-service uniprocessor, a duplicate-free set of jobs receives at most
one unit of service per instant. -/
theorem service_of_jobs_le_1 {Job : JobType} [DecidableEq Job]
    {PState : ProcessorState Job} :
    unit_service_proc_model PState → uniprocessor_model PState →
    ∀ (sched : schedule PState) (P : Job → Bool) (jobs : List Job), jobs.Nodup →
      ∀ t : instant, service_of_jobs_at sched P jobs t ≤ 1 := by
  intro hu huni sched P jobs hnd t
  unfold service_of_jobs_at
  induction jobs with
  | nil => simp [sf_nil]
  | cons a L ih =>
    rw [List.nodup_cons] at hnd
    rw [sf_cons]
    rcases service_is_zero_or_one hu sched a t with h0 | h1
    · have := ih hnd.2
      cases P a <;> simp only [cond_true, cond_false] <;> omega'
    · have hz : sumFiltered L P (fun j => service_at sched j t) = 0 := by
        apply sf_zero
        intro x hx _
        rcases service_is_zero_or_one hu sched x t with hx0 | hx1
        · exact hx0
        · exfalso
          have hsa := service_at_implies_scheduled_at sched a t (by omega')
          have hsx := service_at_implies_scheduled_at sched x t (by omega')
          have := huni a x sched t hsa hsx
          subst this
          exact hnd.1 hx
      rw [hz]
      cases P a <;> simp only [cond_true, cond_false] <;> omega'

/-- The service of the jobs in `[t, t + Δ)` is at most `Δ`. -/
theorem service_of_jobs_le_length_of_interval {Job : JobType} [DecidableEq Job]
    {PState : ProcessorState Job} :
    unit_service_proc_model PState → uniprocessor_model PState →
    ∀ (sched : schedule PState) (P : Job → Bool) (jobs : List Job), jobs.Nodup →
      ∀ (t : instant) (Δ : duration), service_of_jobs sched P jobs t (t + Δ) ≤ Δ := by
  intro hu huni sched P jobs hnd t Δ
  rw [service_of_jobs_sum_over_time_interval]
  calc (∑ x ∈ Finset.Ico t (t + Δ), service_of_jobs_at sched P jobs x)
      ≤ ∑ _x ∈ Finset.Ico t (t + Δ), 1 :=
        Finset.sum_le_sum (fun x _ => service_of_jobs_le_1 hu huni sched P jobs hnd x)
    _ = Δ := by simp

/-- The service of the jobs in `[t1, t2)` is at most `t2 - t1`. -/
theorem service_of_jobs_le_length_of_interval' {Job : JobType} [DecidableEq Job]
    {PState : ProcessorState Job} :
    unit_service_proc_model PState → uniprocessor_model PState →
    ∀ (sched : schedule PState) (P : Job → Bool) (jobs : List Job), jobs.Nodup →
      ∀ t1 t2 : instant, service_of_jobs sched P jobs t1 t2 ≤ t2 - t1 := by
  intro hu huni sched P jobs hnd t1 t2
  rw [service_of_jobs_sum_over_time_interval]
  calc (∑ x ∈ Finset.Ico t1 t2, service_of_jobs_at sched P jobs x)
      ≤ ∑ _x ∈ Finset.Ico t1 t2, 1 :=
        Finset.sum_le_sum (fun x _ => service_of_jobs_le_1 hu huni sched P jobs hnd x)
    _ = t2 - t1 := by simp

/-- On an ideal-progress unit-service uniprocessor, the service at `t` is one
when some job of the set satisfying `P` is scheduled. -/
theorem service_of_jobs_at_scheduled1 {Job : JobType} [DecidableEq Job]
    {PState : ProcessorState Job} :
    unit_service_proc_model PState → uniprocessor_model PState →
    ∀ (sched : schedule PState) (P : Job → Bool), ideal_progress_proc_model PState →
    ∀ js : List Job, js.Nodup →
      ∀ t : instant,
        (∃ j : Job, decide (j ∈ js) = true ∧ scheduled_at sched j t = true ∧ P j = true) →
          service_of_jobs_at sched P js t = 1 := by
  intro hu huni sched P hprog js hnd t ⟨j, hjm, hsj, hPj⟩
  have hother : ∀ x, x ≠ j → service_at sched x t = 0 := by
    intro x hne
    apply not_scheduled_implies_no_service sched x t
    cases hs : scheduled_at sched x t
    · rfl
    · exact absurd (huni x j sched t hs hsj) hne
  have hjm' := of_decide_eq_true hjm
  unfold service_of_jobs_at
  clear hjm
  induction js with
  | nil => exact absurd hjm' List.not_mem_nil
  | cons a L ih =>
    rw [List.nodup_cons] at hnd
    rw [sf_cons]
    by_cases ha : a = j
    · subst ha
      have hz : sumFiltered L P (fun x => service_at sched x t) = 0 :=
        sf_zero _ _ _ (fun x hx _ => hother x (fun e => hnd.1 (e ▸ hx)))
      rw [hz, hPj]
      simp only [cond_true]
      rw [unit_service_at1 sched a hprog hu t hsj]
    · have hL : j ∈ L := by
        rcases List.mem_cons.mp hjm' with e | h
        · exact absurd e.symm ha
        · exact h
      rw [ih hnd.2 hL, hother a ha]
      cases P a <;> rfl

/-- If some job of the set satisfying `P` is scheduled at every instant of
`[t1, t2)`, the service in that interval is `t2 - t1`. -/
theorem service_of_jobs_always_scheduled {Job : JobType} [DecidableEq Job]
    {PState : ProcessorState Job} :
    unit_service_proc_model PState → uniprocessor_model PState →
    ∀ (sched : schedule PState) (P : Job → Bool), ideal_progress_proc_model PState →
    ∀ js : List Job, js.Nodup →
      ∀ t1 t2 : Nat,
        (∀ t : Nat, (decide (t1 ≤ t) && decide (t < t2)) = true →
          ∃ j : Job, decide (j ∈ js) = true ∧ scheduled_at sched j t = true ∧ P j = true) →
        service_of_jobs sched P js t1 t2 = t2 - t1 := by
  intro hu huni sched P hprog js hnd t1 t2 h
  rw [service_of_jobs_sum_over_time_interval]
  rw [Finset.sum_congr rfl (fun x hx => service_of_jobs_at_scheduled1 hu huni sched P hprog
    js hnd x (h x (by rw [Finset.mem_Ico] at hx; simp [hx.1, hx.2])))]
  simp

/-- On a duplicate-free list, the per-instant service of the jobs satisfying
`P` is the indicator of some such job receiving service. -/
private theorem sf_service_at_eq_any {Job : JobType} [DecidableEq Job]
    {PState : ProcessorState Job} (hu : unit_service_proc_model PState)
    (huni : uniprocessor_model PState) (sched : schedule PState) (P : Job → Bool)
    (L : List Job) (hnd : L.Nodup) (x : instant) :
    sumFiltered L P (fun j => service_at sched j x) =
      (L.any (fun j => P j && receives_service_at sched j x)).toNat := by
  have hle := service_of_jobs_le_1 hu huni sched P L hnd x
  unfold service_of_jobs_at at hle
  have hgt := sum_nat_gt0 L P (fun j => service_at sched j x)
  unfold receives_service_at
  rw [← hgt]
  cases hd : decide (0 < sumFiltered L P (fun j => service_at sched j x))
  · have := of_decide_eq_false hd
    simp only [Bool.toNat_false]; omega
  · have := of_decide_eq_true hd
    simp only [Bool.toNat_true]; omega

/-- The number of instants in `[t1, t)` at which some served job satisfies `P`
equals the service of the jobs satisfying `P` that arrive in `[t1, t)`,
provided `t1` is a quiet time and `P` implies higher-or-equal priority. -/
theorem cumulative_pred_served_eq_service {Job : JobType} [DecidableEq Job]
    [JobArrival Job] [JobCost Job] {PState : ProcessorState Job} :
    unit_service_proc_model PState → uniprocessor_model PState →
    ∀ arr_seq : arrival_sequence Job, consistent_arrival_times arr_seq →
    ∀ sched : schedule PState, jobs_must_arrive_to_execute sched →
      completed_jobs_dont_execute sched →
    ∀ P : Job → Bool, arrival_sequence_uniq arr_seq →
    ∀ (JLFP : JLFP_policy Job) (j : Job) (t1 t : instant),
      quiet_time arr_seq sched j t1 →
      (∀ j' : Job, P j' = true → hep_job j' j = true) →
      ∑ t' ∈ (Finset.Ico t1 t : Finset Nat), ((served_jobs_at arr_seq sched t').any P).toNat =
        service_of_jobs sched P (arrivals_between arr_seq t1 t) t1 t := by
  intro hu huni arr_seq hc sched hmust hcd P huq _JLFP j t1 t hquiet Phep
  rw [service_of_jobs_sum_over_time_interval]
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finset.mem_Ico] at hx
  unfold service_of_jobs_at
  rw [sf_service_at_eq_any hu huni sched P _ (arrivals_uniq arr_seq hc huq t1 t) x]
  congr 1
  unfold served_jobs_at arrivals_up_to
  rw [List.any_filter]
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true, Bool.and_eq_true]
  constructor
  · rintro ⟨jo, hmem, hrecv, hPjo⟩
    have hsched := service_at_implies_scheduled_at sched jo x (of_decide_eq_true hrecv)
    have harr := in_arrivals_implies_arrived arr_seq jo 0 (x + 1) (decide_eq_true hmem)
    have hlt := job_arrival_between_lt arr_seq hc jo 0 (x + 1) (decide_eq_true hmem)
    refine ⟨jo, ?_, hPjo, hrecv⟩
    by_cases hge : t1 ≤ job_arrival jo
    · exact of_decide_eq_true (job_in_arrivals_between arr_seq hc jo t1 t harr hge (by omega'))
    · exfalso
      have hcomp := hquiet jo harr (Phep jo hPjo) (by unfold arrived_before; simp; omega')
      have hcomp' := completion_monotonic sched jo t1 x hx.1 hcomp
      have hnc := scheduled_implies_not_completed sched jo hcd x hsched
      rw [hcomp'] at hnc
      exact absurd hnc (by decide)
  · rintro ⟨jo, hmem, hPjo, hrecv⟩
    have hsched := service_at_implies_scheduled_at sched jo x (of_decide_eq_true hrecv)
    have hhas := hmust jo x hsched
    unfold has_arrived at hhas
    have harr := in_arrivals_implies_arrived arr_seq jo t1 t (decide_eq_true hmem)
    refine ⟨jo, ?_, hrecv, hPjo⟩
    exact of_decide_eq_true (job_in_arrivals_between arr_seq hc jo 0 (x + 1) harr
      (Nat.zero_le _) (by have := of_decide_eq_true hhas; omega'))

end Prosa.Analysis.Facts.Model.ServiceOfJobs
