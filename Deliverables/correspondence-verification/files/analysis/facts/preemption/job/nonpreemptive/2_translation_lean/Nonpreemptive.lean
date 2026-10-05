-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/facts/preemption/job/nonpreemptive.v

import Prosa.Model.Job.Properties
import Prosa.Model.Schedule.Nonpreemptive
import Prosa.Model.Preemption.FullyNonpreemptive
import Prosa.Analysis.Facts.Behavior.All

namespace Prosa.Analysis.Facts.Preemption.Job.Nonpreemptive

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Behavior.Ready
open Prosa.Behavior.Time
open Prosa.Model.Processor.PlatformProperties
open Prosa.Model.Preemption.Parameter
open Prosa.Model.Preemption.FullyNonpreemptive
open Prosa.Model.Schedule.Nonpreemptive
open Prosa.Analysis.Facts.Behavior.Service
open Prosa.Analysis.Facts.Behavior.Completion
open Prosa.Util.List
open Prosa.Util.Nondecreasing

/-! Representation notes: the source enables the section-local
`fully_nonpreemptive_job_model` instance with `#[local] Existing Instance`;
the statements pass the accepted Lean definition of the same name explicitly,
as the elaborated source types do; `~~ b` in `Prop` position is
`(!b) = true`. Binder orders follow the elaborated types (unused section
context and hypotheses are absent, as in the elaborated source). -/

/-- LEAN_HELPER: filtering `[1, n]` by "is zero or equals `c`" keeps exactly
`c` when `n = c`, and nothing when `n < c`. -/
private theorem filter_range'_one (c : Nat) :
    ∀ n : Nat, n ≤ c →
      (List.range' 1 n).filter (fun ρ => decide (ρ = 0) || decide (ρ = c)) =
        if n = c ∧ 0 < c then [c] else [] := by
  intro n
  induction n with
  | zero =>
    intro _
    by_cases h : 0 = c ∧ 0 < c
    · omega
    · rw [if_neg h]; rfl
  | succ n ih =>
    intro hn
    rw [List.range'_concat, List.filter_append, ih (Nat.le_of_succ_le hn)]
    have hne : ¬ (n = c ∧ 0 < c) := by omega
    rw [if_neg hne, List.nil_append]
    simp only [List.filter_cons, List.filter_nil]
    by_cases h : n + 1 = c
    · rw [if_pos (⟨h, by omega⟩ : n + 1 = c ∧ 0 < c)]
      have hc : 1 + 1 * n = c := by omega
      rw [hc]; simp
    · rw [if_neg (by omega : ¬ (n + 1 = c ∧ 0 < c))]
      have h0 : decide (1 + 1 * n = 0) = false := by simp
      have hc : decide (1 + 1 * n = c) = false := by simp; omega
      rw [h0, hc]; rfl

/-- LEAN_HELPER: the preemption points of the fully nonpreemptive model. -/
private theorem fnp_preemption_points {Job : JobType} [DecidableEq Job] [JobCost Job] (j : Job) :
    @job_preemption_points Job _ _ fully_nonpreemptive_job_model j =
      if job_cost j = 0 then [0] else [0, job_cost j] := by
  show (range 0 (job_cost j)).filter (fun ρ => decide (ρ = 0) || decide (ρ = job_cost j)) = _
  unfold range index_iota
  rw [Nat.sub_zero, List.range'_succ, List.filter_cons]
  have hf := filter_range'_one (job_cost j) (job_cost j) (Nat.le_refl _)
  by_cases h : job_cost j = 0
  · rw [if_pos h]
    have hf' : (List.range' (0 + 1) (job_cost j)).filter
        (fun ρ => decide (ρ = 0) || decide (ρ = job_cost j)) = [] := by
      rw [h]; rfl
    simp [hf']
  · rw [if_neg h]
    have hc : (job_cost j = job_cost j ∧ 0 < job_cost j) := ⟨rfl, Nat.pos_of_ne_zero h⟩
    rw [if_pos hc] at hf
    simp [hf]

/-- The fully nonpreemptive model is a valid preemption model. -/
theorem valid_fully_nonpreemptive_model {Job : JobType} [DecidableEq Job] [JobCost Job]
    (arr_seq : arrival_sequence Job) {PState : ProcessorState Job} :
    unit_service_proc_model PState →
      ∀ sched : schedule PState, nonpreemptive_schedule sched →
        completed_jobs_dont_execute sched →
          @valid_preemption_model Job _ _ fully_nonpreemptive_job_model PState arr_seq sched := by
  intro H_unit sched H_np H_cjde j _
  refine ⟨rfl, ?_, ?_, ?_⟩
  · change (decide (job_cost j = 0) || decide (job_cost j = job_cost j)) = true
    simp
  · intro t h
    change (!(decide (service sched j t = 0) || decide (service sched j t = job_cost j))) = true at h
    simp only [Bool.not_or, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at h
    obtain ⟨hpos, hneq⟩ := h
    have hle := service_at_most_cost sched H_cjde j H_unit t
    obtain ⟨ft, hft, hsched, _⟩ :=
      incremental_service_during sched H_unit j 0 t 0 (Nat.pos_of_ne_zero hpos)
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hft
    apply H_np j ft t (Nat.le_of_lt hft.2) hsched
    simp only [completed_by, Bool.not_eq_true', decide_eq_false_iff_not]
    exact Nat.not_le.mpr (Nat.lt_of_le_of_ne hle hneq)
  · intro prt hns hs
    change (decide (service sched j (prt + 1) = 0) ||
      decide (service sched j (prt + 1) = job_cost j)) = true
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    left
    by_contra hpos
    obtain ⟨ft, hft, hsched, _⟩ :=
      incremental_service_during sched H_unit j 0 (prt + 1) 0 (Nat.pos_of_ne_zero hpos)
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hft
    have hlt := H_cjde j (prt + 1) hs
    have hmono := service_monotonic sched j prt (prt + 1) (Nat.le_succ _)
    have hsp := H_np j ft prt (Nat.le_of_lt_succ hft.2) hsched (by
      simp only [completed_by, Bool.not_eq_true', decide_eq_false_iff_not]
      exact Nat.not_le.mpr (Nat.lt_of_le_of_lt hmono hlt))
    simp [hsp] at hns

/-- Under the fully nonpreemptive model the longest nonpreemptive segment is
the job cost. -/
theorem job_max_nps_is_job_cost {Job : JobType} [DecidableEq Job] [JobCost Job] :
    ∀ j : Job,
      @job_max_nonpreemptive_segment Job _ _ fully_nonpreemptive_job_model j = job_cost j := by
  intro j
  unfold job_max_nonpreemptive_segment lengths_of_segments
  rw [fnp_preemption_points]
  by_cases h : job_cost j = 0
  · simp [h, distances, max0]
  · simp [h, distances, max0]

/-- Under the fully nonpreemptive model the last nonpreemptive segment is the
job cost. -/
theorem job_last_nps_is_job_cost {Job : JobType} [DecidableEq Job] [JobCost Job] :
    ∀ j : Job,
      @job_last_nonpreemptive_segment Job _ _ fully_nonpreemptive_job_model j = job_cost j := by
  intro j
  unfold job_last_nonpreemptive_segment lengths_of_segments
  rw [fnp_preemption_points]
  by_cases h : job_cost j = 0
  · simp [h, distances, last0]
  · simp [h, distances, last0]

/-- A schedule without preemptions is exactly a nonpreemptive schedule. -/
theorem no_preemptions_equiv_nonpreemptive {Job : JobType} [DecidableEq Job] [JobCost Job]
    {PState : ProcessorState Job} (sched : schedule PState) :
    (∀ (j : Job) (t : instant), (!preempted_at sched j t) = true) ↔ nonpreemptive_schedule sched := by
  constructor
  · intro NP j t t' hle hs hinc
    dsimp only [instant] at t t' hle
    induction t' with
    | zero =>
      have : t = 0 := by omega
      subst this; exact hs
    | succ t' ih =>
      rcases Nat.lt_or_ge t (t' + 1) with hlt | hge
      · have hinc' : (!completed_by sched j t') = true := by
          cases hc : completed_by sched j t' with
          | false => rfl
          | true =>
            have := completion_monotonic sched j t' (t' + 1) (Nat.le_succ _) hc
            simp [this] at hinc
        have hs' := ih (by omega) hinc'
        cases hsn : scheduled_at sched j (t' + 1) with
        | true => rfl
        | false =>
          have := NP j (t' + 1)
          simp [preempted_at, hs', hinc, hsn] at this
      · have : t = t' + 1 := by omega
        subst this; exact hs
  · intro H j t
    dsimp only [instant] at t
    cases hp : preempted_at sched j t with
    | false => rfl
    | true =>
      simp only [preempted_at, Bool.and_eq_true, Bool.not_eq_true'] at hp
      obtain ⟨⟨hs, hinc⟩, hns⟩ := hp
      have := H j (t - 1) t (Nat.sub_le _ _) hs (by simp [hinc])
      simp [this] at hns

end Prosa.Analysis.Facts.Preemption.Job.Nonpreemptive
