-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/facts/transform/edf_opt.v

import Prosa.Analysis.Transform.EdfTrans
import Prosa.Analysis.Facts.Transform.Swaps
import Prosa.Analysis.Facts.Readiness.Basic
import Prosa.Analysis.Definitions.Schedulability
import Prosa.Analysis.Facts.Behavior.Deadlines
import Prosa.Analysis.Facts.Behavior.Completion
import Prosa.Analysis.Facts.Behavior.Service
import Prosa.Model.Schedule.Edf

namespace Prosa.Analysis.Facts.Transform.EdfOpt

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Ready
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Behavior.Time
open Prosa.Model.Processor.Ideal
open Prosa.Model.Processor.PlatformProperties
open Prosa.Model.Readiness.Basic
open Prosa.Model.Schedule.Edf
open Prosa.Util.SearchArg
open Prosa.Analysis.Transform.Swap
open Prosa.Analysis.Transform.Prefix
open Prosa.Analysis.Transform.EdfTrans
open Prosa.Analysis.Definitions.SchedulePrefix
open Prosa.Analysis.Definitions.Schedulability
open Prosa.Analysis.Facts.Transform.Swaps
open Prosa.Analysis.Facts.Model.Ideal.Schedule
open Prosa.Analysis.Facts.Behavior.Deadlines
open Prosa.Analysis.Facts.Behavior.Completion
open Prosa.Analysis.Facts.Behavior.Service
open Prosa.Analysis.Facts.Behavior.Arrivals
open Prosa.Analysis.Facts.Readiness.Basic

/-! The main argument of the EDF optimality proof: properties of `find_swap_candidate`, `make_edf_at`, the EDF
prefix transformation and the full EDF transformation, and finally EDF optimality.

Binders follow the elaborated source types: each statement takes the section inputs and hypotheses it uses, in
their elaborated order. The ideal processor `ideal.processor_state Job` is the accepted `processor_state Job`
(states `Option Job`). Representation: a Boolean in `Prop` position is `= true`; `a <= b < c` is
`(decide (a ≤ b) && decide (b < c)) = true`; `t.+1` is `t + 1`; the section-local `Let`s `sched'`, `sched_edf`
and `equivalent_edf_schedule` are unfolded; the section-local `basic_ready_instance` of the optimality section is
the accepted instance, passed explicitly where the elaborated statements use it. -/

/-- `omega` after unfolding the time aliases. -/
macro "omega'" : tactic => `(tactic| (try dsimp only [instant, duration, work] at *) <;> omega)

section Helpers

variable {Job : JobType} [DecidableEq Job]

/-- LEAN_HELPER: the swapped schedule shows at `t1` what the original shows at `t2`. -/
private theorem swapped_at_t1 (sched : schedule (processor_state Job)) (t1 t2 : instant) :
    swapped sched t1 t2 t1 = sched t2 := by
  unfold swapped replace_at
  by_cases h : t2 = t1
  · subst h; simp
  · simp [h]

/-- LEAN_HELPER: `scheduled_at` on the ideal processor as an equation on the state. -/
private theorem sched_of_scheduled (sched : schedule (processor_state Job)) (j : Job) (t : instant)
    (h : scheduled_at sched j t = true) : sched t = some j := by
  rw [scheduled_at_def] at h
  simpa using h

private theorem scheduled_of_sched (sched : schedule (processor_state Job)) (j : Job) (t : instant)
    (h : sched t = some j) : scheduled_at sched j t = true := by
  rw [scheduled_at_def]
  simpa using h

end Helpers

section FindSwapCandidateFacts

variable {Job : JobType} [DecidableEq Job]

/-- The processor state at a time at which a job is scheduled is relevant. -/
theorem t1_relevant [JobArrival Job] (sched : schedule (processor_state Job)) :
    jobs_must_arrive_to_execute sched →
      ∀ (j1 : Job) (t1 : instant), scheduled_at sched j1 t1 = true → relevant_pstate t1 (sched t1) = true := by
  intro hmust j1 t1 hs
  rw [sched_of_scheduled sched j1 t1 hs]
  exact hmust j1 t1 hs

/-- The search for a relevant state succeeds. -/
theorem fsc_search_successful [JobDeadline Job] [JobArrival Job] (sched : schedule (processor_state Job)) :
    jobs_must_arrive_to_execute sched →
      ∀ (j1 : Job) (t1 : instant), scheduled_at sched j1 t1 = true → t1 < job_deadline j1 →
        ∃ t : Nat, search_arg sched (relevant_pstate t1) earlier_deadline t1 (job_deadline j1) = some t := by
  intro hmust j1 t1 hs hdl
  exact search_arg_not_none sched (relevant_pstate t1) earlier_deadline t1 (job_deadline j1)
    ⟨t1, ⟨Nat.le_refl _, hdl⟩, t1_relevant sched hmust j1 t1 hs⟩

/-- The search yields `find_swap_candidate`. -/
theorem fsc_search_result [JobDeadline Job] [JobArrival Job] (sched : schedule (processor_state Job)) :
    jobs_must_arrive_to_execute sched →
      ∀ (j1 : Job) (t1 : instant), scheduled_at sched j1 t1 = true → t1 < job_deadline j1 →
        search_arg sched (relevant_pstate t1) earlier_deadline t1 (job_deadline j1) =
          some (find_swap_candidate sched t1 j1) := by
  intro hmust j1 t1 hs hdl
  obtain ⟨t, ht⟩ := fsc_search_successful sched hmust j1 t1 hs hdl
  unfold find_swap_candidate
  rw [ht]

/-- A job arriving by `t1` is scheduled at the found time. -/
theorem fsc_not_idle [JobDeadline Job] [JobArrival Job] (sched : schedule (processor_state Job)) :
    jobs_must_arrive_to_execute sched →
      ∀ (j1 : Job) (t1 : instant), scheduled_at sched j1 t1 = true → t1 < job_deadline j1 →
        ∃ j' : Job, scheduled_at sched j' (find_swap_candidate sched t1 j1) = true ∧ job_arrival j' ≤ t1 := by
  intro hmust j1 t1 hs hdl
  have hres := fsc_search_result sched hmust j1 t1 hs hdl
  have hpred := search_arg_pred sched (relevant_pstate t1) earlier_deadline t1 (job_deadline j1) _ hres
  cases hst : sched (find_swap_candidate sched t1 j1) with
  | none => rw [hst] at hpred; simp [relevant_pstate] at hpred
  | some j' =>
    rw [hst] at hpred
    exact ⟨j', scheduled_of_sched sched j' _ hst, of_decide_eq_true hpred⟩

/-- Any job scheduled at the found time arrives by `t1`. -/
theorem fsc_found_job_arrival [JobDeadline Job] [JobArrival Job] (sched : schedule (processor_state Job)) :
    jobs_must_arrive_to_execute sched →
      ∀ (j1 : Job) (t1 : instant), scheduled_at sched j1 t1 = true → t1 < job_deadline j1 →
        ∀ j2 : Job, scheduled_at sched j2 (find_swap_candidate sched t1 j1) = true → job_arrival j2 ≤ t1 := by
  intro hmust j1 t1 hs hdl j2 hs2
  obtain ⟨j', hs', harr⟩ := fsc_not_idle sched hmust j1 t1 hs hdl
  rw [← ideal_proc_model_is_a_uniprocessor_model Job j' j2 sched _ hs' hs2]
  exact harr

/-- The found time lies in `[t1, job_deadline j1)`. -/
theorem fsc_range [JobDeadline Job] [JobArrival Job] (sched : schedule (processor_state Job)) :
    jobs_must_arrive_to_execute sched →
      ∀ (j1 : Job) (t1 : instant), scheduled_at sched j1 t1 = true → t1 < job_deadline j1 →
        (decide (t1 ≤ find_swap_candidate sched t1 j1) &&
          decide (find_swap_candidate sched t1 j1 < job_deadline j1)) = true := by
  intro hmust j1 t1 hs hdl
  have h := search_arg_in_range sched (relevant_pstate t1) earlier_deadline t1 (job_deadline j1) _
    (fsc_search_result sched hmust j1 t1 hs hdl)
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact h

/-- The lower bound of `fsc_range`. -/
theorem fsc_range1 [JobDeadline Job] [JobArrival Job] (sched : schedule (processor_state Job)) :
    jobs_must_arrive_to_execute sched →
      ∀ (j1 : Job) (t1 : instant), scheduled_at sched j1 t1 = true → t1 < job_deadline j1 →
        t1 ≤ find_swap_candidate sched t1 j1 := by
  intro hmust j1 t1 hs hdl
  have h := fsc_range sched hmust j1 t1 hs hdl
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1

/-- The job at the found time has a deadline no later than any job scheduled in the window that arrived by `t1`. -/
theorem fsc_found_job_deadline [JobDeadline Job] [JobArrival Job] (sched : schedule (processor_state Job)) :
    jobs_must_arrive_to_execute sched →
      ∀ (j1 : Job) (t1 : instant), scheduled_at sched j1 t1 = true → t1 < job_deadline j1 →
        ∀ j2 : Job, scheduled_at sched j2 (find_swap_candidate sched t1 j1) = true →
          ∀ (j : Job) (t : Nat), (decide (t1 ≤ t) && decide (t < job_deadline j1)) = true →
            scheduled_at sched j t = true → job_arrival j ≤ t1 → job_deadline j2 ≤ job_deadline j := by
  intro hmust j1 t1 hs hdl j2 hs2 j t hrange hsj harr
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hrange
  have hrefl : ∀ x : (processor_state Job).State, earlier_deadline x x = true := by
    intro x; unfold earlier_deadline; exact decide_eq_true (Nat.le_refl _)
  have htrans : ∀ x y z : (processor_state Job).State, earlier_deadline x y = true →
      earlier_deadline y z = true → earlier_deadline x z = true := by
    intro x y z hxy hyz; unfold earlier_deadline at *
    exact decide_eq_true (Nat.le_trans (of_decide_eq_true hxy) (of_decide_eq_true hyz))
  have htotal : ∀ x y : (processor_state Job).State, earlier_deadline x y = true ∨ earlier_deadline y x = true := by
    intro x y; unfold earlier_deadline
    rcases Nat.le_total ((match x with | none => 0 | some j => job_deadline j))
        ((match y with | none => 0 | some j => job_deadline j)) with h | h
    · exact Or.inl (decide_eq_true h)
    · exact Or.inr (decide_eq_true h)
  have hsjt := sched_of_scheduled sched j t hsj
  have hed := search_arg_extremum sched (relevant_pstate t1) earlier_deadline hrefl htrans htotal t1
    (job_deadline j1) _ (fsc_search_result sched hmust j1 t1 hs hdl) t hrange
    (by rw [hsjt]; exact decide_eq_true harr)
  rw [sched_of_scheduled sched j2 _ hs2, hsjt] at hed
  exact of_decide_eq_true hed

/-- The job at the found time has a deadline no later than `j1`. -/
theorem fsc_no_later_deadline [JobDeadline Job] [JobArrival Job] (sched : schedule (processor_state Job)) :
    jobs_must_arrive_to_execute sched →
      ∀ (j1 : Job) (t1 : instant), scheduled_at sched j1 t1 = true → t1 < job_deadline j1 →
        ∀ j2 : Job, scheduled_at sched j2 (find_swap_candidate sched t1 j1) = true →
          job_deadline j2 ≤ job_deadline j1 := by
  intro hmust j1 t1 hs hdl j2 hs2
  exact fsc_found_job_deadline sched hmust j1 t1 hs hdl j2 hs2 j1 t1
    (by simp only [Bool.and_eq_true, decide_eq_true_eq]; exact ⟨Nat.le_refl _, hdl⟩) hs
    (of_decide_eq_true (hmust j1 t1 hs))

end FindSwapCandidateFacts

section MakeEDFAtFacts

variable {Job : JobType} [DecidableEq Job]

/-- A job scheduled in a schedule without deadline misses has its deadline after the scheduled time. -/
theorem scheduled_job_in_sched_has_later_deadline [JobCost Job] [JobDeadline Job]
    (sched : schedule (processor_state Job)) :
    completed_jobs_dont_execute sched → all_deadlines_met sched →
      ∀ (j : Job) (t : instant), scheduled_at sched j t = true → t < job_deadline j := by
  intro hcde hdm j t hs
  exact scheduled_at_implies_later_deadline sched hcde j t (hdm j t hs) hs

/-- `make_edf_at` preserves that completed jobs do not execute. -/
theorem mea_completed_jobs [JobCost Job] [JobDeadline Job] [JobArrival Job]
    (sched : schedule (processor_state Job)) :
    jobs_must_arrive_to_execute sched → completed_jobs_dont_execute sched → all_deadlines_met sched →
      ∀ t_edf : instant, completed_jobs_dont_execute (make_edf_at sched t_edf) := by
  intro hmust hcde hdm t_edf
  unfold make_edf_at
  cases h : sched t_edf with
  | none => exact hcde
  | some j_orig =>
    have hs := scheduled_of_sched sched j_orig t_edf h
    exact swapped_completed_jobs_dont_execute sched t_edf _
      (fsc_range1 sched hmust j_orig t_edf hs (scheduled_job_in_sched_has_later_deadline sched hcde hdm _ _ hs))
      (ideal_proc_model_provides_unit_service Job) (ideal_proc_model_ensures_ideal_progress Job) hcde

/-- `make_edf_at` introduces no deadline misses. -/
theorem mea_no_deadline_misses [JobCost Job] [JobDeadline Job] [JobArrival Job]
    (sched : schedule (processor_state Job)) :
    jobs_must_arrive_to_execute sched → completed_jobs_dont_execute sched → all_deadlines_met sched →
      ∀ t_edf : instant, all_deadlines_met (make_edf_at sched t_edf) := by
  intro hmust hcde hdm t_edf j t hsj
  unfold make_edf_at at hsj ⊢
  cases h : sched t_edf with
  | none => rw [h] at hsj; exact hdm j t hsj
  | some j_orig =>
    rw [h] at hsj
    have hs := scheduled_of_sched sched j_orig t_edf h
    have hdl := scheduled_job_in_sched_has_later_deadline sched hcde hdm _ _ hs
    obtain ⟨t', ht'⟩ := swap_job_scheduled sched t_edf _ j t hsj
    apply edf_swap_no_deadline_misses_introduced sched hcde t_edf _ (fsc_range1 sched hmust j_orig t_edf hs hdl)
    · intro j1 j2 hs1 hs2
      have hj1 : j_orig = j1 := ideal_proc_model_is_a_uniprocessor_model Job j_orig j1 sched t_edf hs hs1
      subst hj1
      exact fsc_found_job_deadline sched hmust j_orig t_edf hs hdl j2 hs2 j_orig t_edf
        (by simp only [Bool.and_eq_true, decide_eq_true_eq]; exact ⟨Nat.le_refl _, hdl⟩) hs
        (of_decide_eq_true (hmust j_orig t_edf hs))
    · intro j1 _
      obtain ⟨j', hs', _⟩ := fsc_not_idle sched hmust j_orig t_edf hs hdl
      exact ⟨j', hs', scheduled_job_in_sched_has_later_deadline sched hcde hdm _ _ hs'⟩
    · exact hdm j t' ht'

/-- Jobs scheduled in `make_edf_at sched t_edf` have their deadlines after the scheduled time. -/
theorem mea_scheduled_job_has_later_deadline [JobCost Job] [JobDeadline Job] [JobArrival Job]
    (sched : schedule (processor_state Job)) :
    jobs_must_arrive_to_execute sched → completed_jobs_dont_execute sched → all_deadlines_met sched →
      ∀ (t_edf : instant) (j : Job) (t : instant), scheduled_at (make_edf_at sched t_edf) j t = true →
        t < job_deadline j := by
  intro hmust hcde hdm t_edf j t hs
  exact scheduled_at_implies_later_deadline _ (mea_completed_jobs sched hmust hcde hdm t_edf) j t
    (mea_no_deadline_misses sched hmust hcde hdm t_edf j t hs) hs

/-- The job originally scheduled at `t_edf` has its deadline after `t_edf`. -/
theorem mea_guarantee_dl_orig [JobCost Job] [JobDeadline Job] (sched : schedule (processor_state Job)) :
    completed_jobs_dont_execute sched → all_deadlines_met sched →
      ∀ (t_edf : instant) (j_orig : Job), scheduled_at sched j_orig t_edf = true → t_edf < job_deadline j_orig := by
  intro hcde hdm t_edf j_orig hs
  exact scheduled_job_in_sched_has_later_deadline sched hcde hdm j_orig t_edf hs

/-- The job scheduled at `t_edf` after the swap is the one found by `find_swap_candidate`. -/
theorem mea_guarantee_fsc_is_j_edf [JobDeadline Job] [JobArrival Job] (sched : schedule (processor_state Job))
    (t_edf : instant) (j_orig : Job) :
    scheduled_at sched j_orig t_edf = true →
      ∀ j_edf : Job, scheduled_at (make_edf_at sched t_edf) j_edf t_edf = true →
        sched (find_swap_candidate sched t_edf j_orig) = some j_edf := by
  intro hs j_edf hse
  have h := sched_of_scheduled sched j_orig t_edf hs
  have he := sched_of_scheduled _ j_edf t_edf hse
  unfold make_edf_at at he
  rw [h] at he
  simp only at he
  rw [swapped_at_t1] at he
  exact he

/-- The job scheduled at `t_edf` after the swap has a deadline no later than the original job. -/
theorem mea_guarantee_deadlines [JobCost Job] [JobDeadline Job] [JobArrival Job]
    (sched : schedule (processor_state Job)) :
    jobs_must_arrive_to_execute sched → completed_jobs_dont_execute sched → all_deadlines_met sched →
      ∀ (t_edf : instant) (j_orig : Job), scheduled_at sched j_orig t_edf = true →
        ∀ j_edf : Job, scheduled_at (make_edf_at sched t_edf) j_edf t_edf = true →
          job_deadline j_edf ≤ job_deadline j_orig := by
  intro hmust hcde hdm t_edf j_orig hs j_edf hse
  exact fsc_no_later_deadline sched hmust j_orig t_edf hs
    (mea_guarantee_dl_orig sched hcde hdm t_edf j_orig hs) j_edf
    (scheduled_of_sched sched j_edf _ (mea_guarantee_fsc_is_j_edf sched t_edf j_orig hs j_edf hse))

/-- Case `job_deadline j_orig ≤ t'`. -/
theorem mea_guarantee_case_t'_past_deadline [JobCost Job] [JobDeadline Job] [JobArrival Job]
    (sched : schedule (processor_state Job)) :
    jobs_must_arrive_to_execute sched → completed_jobs_dont_execute sched → all_deadlines_met sched →
      ∀ (t_edf : instant) (j_orig : Job), scheduled_at sched j_orig t_edf = true →
        ∀ j_edf : Job, scheduled_at (make_edf_at sched t_edf) j_edf t_edf = true →
          ∀ (j' : Job) (t' : instant), scheduled_at (make_edf_at sched t_edf) j' t' = true →
            job_deadline j_orig ≤ t' → job_deadline j_edf ≤ job_deadline j' := by
  intro hmust hcde hdm t_edf j_orig hs j_edf hse j' t' hs' hle
  have h1 := mea_guarantee_deadlines sched hmust hcde hdm t_edf j_orig hs j_edf hse
  have h2 := mea_scheduled_job_has_later_deadline sched hmust hcde hdm t_edf j' t' hs'
  omega'

/-- Case `t' < job_deadline j_orig`. -/
theorem mea_guarantee_case_t'_before_deadline [JobCost Job] [JobDeadline Job] [JobArrival Job]
    (sched : schedule (processor_state Job)) :
    jobs_must_arrive_to_execute sched → completed_jobs_dont_execute sched → all_deadlines_met sched →
      ∀ (t_edf : instant) (j_orig : Job), scheduled_at sched j_orig t_edf = true →
        ∀ j_edf : Job, scheduled_at (make_edf_at sched t_edf) j_edf t_edf = true →
          ∀ (j' : Job) (t' : instant), t_edf ≤ t' → scheduled_at (make_edf_at sched t_edf) j' t' = true →
            job_arrival j' ≤ t_edf → t' < job_deadline j_orig → job_deadline j_edf ≤ job_deadline j' := by
  intro hmust hcde hdm t_edf j_orig hs j_edf hse j' t' hle hs' harr hlt
  have h := sched_of_scheduled sched j_orig t_edf hs
  have hdl := mea_guarantee_dl_orig sched hcde hdm t_edf j_orig hs
  have hfsc := mea_guarantee_fsc_is_j_edf sched t_edf j_orig hs j_edf hse
  have hrange := fsc_range sched hmust j_orig t_edf hs hdl
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hrange
  have hsw : make_edf_at sched t_edf = swapped sched t_edf (find_swap_candidate sched t_edf j_orig) := by
    unfold make_edf_at; rw [h]
  rw [hsw] at hs' hse
  obtain ⟨x, hsx, hx1, hx2⟩ : ∃ x, scheduled_at sched j' x = true ∧ t_edf ≤ x ∧ x < job_deadline j_orig := by
    by_cases heq : t_edf = t'
    · subst heq
      refine ⟨find_swap_candidate sched t_edf j_orig, ?_, hrange.1, hrange.2⟩
      rw [← ideal_proc_model_is_a_uniprocessor_model Job j_edf j' _ t_edf hse hs']
      exact scheduled_of_sched sched j_edf _ hfsc
    · by_cases heq' : find_swap_candidate sched t_edf j_orig = t'
      · refine ⟨t_edf, ?_, Nat.le_refl _, hdl⟩
        rw [← heq'] at hs'
        rw [← swap_job_scheduled_t2 sched t_edf (find_swap_candidate sched t_edf j_orig) j']
        exact hs'
      · refine ⟨t', ?_, hle, hlt⟩
        rw [← swap_job_scheduled_other_times sched t_edf (find_swap_candidate sched t_edf j_orig) j' t'
          (decide_eq_true heq) (decide_eq_true heq')]
        exact hs'
  exact fsc_found_job_deadline sched hmust j_orig t_edf hs hdl j_edf (scheduled_of_sched sched j_edf _ hfsc)
    j' x (by simp only [Bool.and_eq_true, decide_eq_true_eq]; exact ⟨hx1, hx2⟩) hsx harr

/-- `make_edf_at` establishes `EDF_at` at `t_edf`. -/
theorem make_edf_at_guarantee [JobCost Job] [JobDeadline Job] [JobArrival Job]
    (sched : schedule (processor_state Job)) :
    jobs_must_arrive_to_execute sched → completed_jobs_dont_execute sched → all_deadlines_met sched →
      ∀ t_edf : instant, EDF_at (make_edf_at sched t_edf) t_edf := by
  intro hmust hcde hdm t_edf j_edf hse t' j' hle hs' harr
  cases h : sched t_edf with
  | none =>
    have he := sched_of_scheduled _ j_edf t_edf hse
    unfold make_edf_at at he
    simp [h] at he
  | some j_orig =>
    have hs := scheduled_of_sched sched j_orig t_edf h
    by_cases hlt : t' < job_deadline j_orig
    · exact mea_guarantee_case_t'_before_deadline sched hmust hcde hdm t_edf j_orig hs j_edf hse j' t' hle hs'
        harr hlt
    · exact mea_guarantee_case_t'_past_deadline sched hmust hcde hdm t_edf j_orig hs j_edf hse j' t' hs'
        (Nat.le_of_not_gt hlt)

/-- `make_edf_at` preserves that jobs must arrive to execute. -/
theorem mea_jobs_must_arrive [JobCost Job] [JobDeadline Job] [JobArrival Job]
    (sched : schedule (processor_state Job)) :
    jobs_must_arrive_to_execute sched → completed_jobs_dont_execute sched → all_deadlines_met sched →
      ∀ t_edf : instant, jobs_must_arrive_to_execute (make_edf_at sched t_edf) := by
  intro hmust hcde hdm t_edf j t hsj
  cases h : sched t_edf with
  | none =>
    have hsw : make_edf_at sched t_edf = sched := by unfold make_edf_at; rw [h]
    rw [hsw] at hsj; exact hmust j t hsj
  | some j_orig =>
    have hs := scheduled_of_sched sched j_orig t_edf h
    have hdl := scheduled_job_in_sched_has_later_deadline sched hcde hdm _ _ hs
    have hsw : make_edf_at sched t_edf = swapped sched t_edf (find_swap_candidate sched t_edf j_orig) := by
      unfold make_edf_at; rw [h]
    rw [hsw] at hsj
    have hr1 := fsc_range1 sched hmust j_orig t_edf hs hdl
    unfold has_arrived
    rcases swap_job_scheduled_cases sched t_edf _ j t hsj with hc | ⟨ht, hc⟩ | ⟨ht, hc⟩
    · rw [hc] at hsj; exact hmust j t hsj
    · rw [hc] at hsj
      have := fsc_found_job_arrival sched hmust j_orig t_edf hs hdl j hsj
      subst ht; exact decide_eq_true this
    · rw [hc] at hsj
      have := of_decide_eq_true (hmust j t_edf hsj)
      subst ht; exact decide_eq_true (Nat.le_trans this hr1)

/-- Jobs scheduled after `make_edf_at` are scheduled somewhere originally. -/
theorem mea_job_scheduled [JobDeadline Job] [JobArrival Job] (sched : schedule (processor_state Job))
    (t_edf : instant) (j : Job) (t : instant) :
    scheduled_at (make_edf_at sched t_edf) j t = true → ∃ t' : instant, scheduled_at sched j t' = true := by
  intro hsj
  unfold make_edf_at at hsj
  cases h : sched t_edf with
  | none => rw [h] at hsj; exact ⟨t, hsj⟩
  | some j_orig => rw [h] at hsj; exact swap_job_scheduled sched t_edf _ j t hsj

/-- Jobs scheduled originally are scheduled somewhere after `make_edf_at`. -/
theorem mea_job_scheduled' [JobDeadline Job] [JobArrival Job] (sched : schedule (processor_state Job))
    (t_edf : instant) (j : Job) (t : instant) :
    scheduled_at sched j t = true → ∃ t' : instant, scheduled_at (make_edf_at sched t_edf) j t' = true := by
  intro hsj
  unfold make_edf_at
  cases h : sched t_edf with
  | none => exact ⟨t, hsj⟩
  | some j_orig => exact swap_job_scheduled_original sched t_edf _ j t hsj

/-- `make_edf_at` preserves that jobs come from the arrival sequence. -/
theorem mea_jobs_come_from_arrival_sequence [JobDeadline Job] [JobArrival Job]
    (sched : schedule (processor_state Job)) (t_edf : instant) (arr_seq : arrival_sequence Job) :
    jobs_come_from_arrival_sequence sched arr_seq →
      jobs_come_from_arrival_sequence (make_edf_at sched t_edf) arr_seq := by
  intro hfrom
  unfold make_edf_at
  cases h : sched t_edf with
  | none => exact hfrom
  | some j_orig => exact swapped_jobs_come_from_arrival_sequence sched t_edf _ arr_seq hfrom

/-- `make_edf_at` grows an EDF prefix by one time unit. -/
theorem mea_EDF_widen [JobCost Job] [JobDeadline Job] [JobArrival Job] (sched : schedule (processor_state Job)) :
    jobs_must_arrive_to_execute sched → completed_jobs_dont_execute sched → all_deadlines_met sched →
      ∀ t_edf : instant, (∀ t : Nat, t < t_edf → EDF_at sched t) →
        ∀ t : Nat, t ≤ t_edf → EDF_at (make_edf_at sched t_edf) t := by
  intro hmust hcde hdm t_edf hpre t hle
  rcases Nat.lt_or_eq_of_le hle with hlt | heq
  · cases h : sched t_edf with
    | none =>
      have hsw : make_edf_at sched t_edf = sched := by unfold make_edf_at; rw [h]
      rw [hsw]; exact hpre t hlt
    | some j_orig =>
      have hs := scheduled_of_sched sched j_orig t_edf h
      have hdl := scheduled_job_in_sched_has_later_deadline sched hcde hdm _ _ hs
      have hr1 := fsc_range1 sched hmust j_orig t_edf hs hdl
      have hsw : make_edf_at sched t_edf = swapped sched t_edf (find_swap_candidate sched t_edf j_orig) := by
        unfold make_edf_at; rw [h]
      rw [hsw]
      intro j hsj t' j' hle' hsj' harr
      have hedf := hpre t hlt
      have hother : scheduled_at (swapped sched t_edf (find_swap_candidate sched t_edf j_orig)) j t =
          scheduled_at sched j t :=
        swap_job_scheduled_other_times sched t_edf _ j t (decide_eq_true (by omega'))
          (decide_eq_true (by omega'))
      rw [hother] at hsj
      rcases swap_job_scheduled_cases sched t_edf _ j' t' hsj' with hc | ⟨ht, hc⟩ | ⟨ht, hc⟩
      · rw [hc] at hsj'; exact hedf j hsj t' j' hle' hsj' harr
      · rw [hc] at hsj'; exact hedf j hsj _ j' (by omega') hsj' harr
      · rw [hc] at hsj'; exact hedf j hsj t_edf j' (by omega') hsj' harr
  · subst heq; exact make_edf_at_guarantee sched hmust hcde hdm t

end MakeEDFAtFacts

section EDFPrefixFacts

variable {Job : JobType} [DecidableEq Job]

/-- The EDF prefix transformation preserves well-formedness and the absence of deadline misses. -/
theorem edf_prefix_well_formedness [JobCost Job] [JobDeadline Job] [JobArrival Job]
    (sched : schedule (processor_state Job)) :
    jobs_must_arrive_to_execute sched → completed_jobs_dont_execute sched → all_deadlines_met sched →
      ∀ horizon : instant,
        completed_jobs_dont_execute (edf_transform_prefix sched horizon) ∧
          jobs_must_arrive_to_execute (edf_transform_prefix sched horizon) ∧
            all_deadlines_met (edf_transform_prefix sched horizon) := by
  intro hmust hcde hdm horizon
  unfold edf_transform_prefix
  apply prefix_map_property_invariance
    (fun s => completed_jobs_dont_execute s ∧ jobs_must_arrive_to_execute s ∧ all_deadlines_met s)
  · intro s t ⟨hc, hm, hd⟩
    exact ⟨mea_completed_jobs s hm hc hd t, mea_jobs_must_arrive s hm hc hd t, mea_no_deadline_misses s hm hc hd t⟩
  · exact ⟨hcde, hmust, hdm⟩

/-- The EDF prefix transformation preserves that jobs must arrive to execute. -/
theorem edf_prefix_jobs_must_arrive [JobCost Job] [JobDeadline Job] [JobArrival Job]
    (sched : schedule (processor_state Job)) :
    jobs_must_arrive_to_execute sched → completed_jobs_dont_execute sched → all_deadlines_met sched →
      ∀ horizon : instant, jobs_must_arrive_to_execute (edf_transform_prefix sched horizon) := by
  intro hmust hcde hdm horizon
  exact (edf_prefix_well_formedness sched hmust hcde hdm horizon).2.1

/-- Jobs scheduled in the EDF prefix have their deadlines after the scheduled time. -/
theorem edf_prefix_scheduled_job_has_later_deadline [JobCost Job] [JobDeadline Job] [JobArrival Job]
    (sched : schedule (processor_state Job)) :
    jobs_must_arrive_to_execute sched → completed_jobs_dont_execute sched → all_deadlines_met sched →
      ∀ (horizon : instant) (j : Job) (t : instant), scheduled_at (edf_transform_prefix sched horizon) j t = true →
        t < job_deadline j := by
  intro hmust hcde hdm horizon j t hs
  obtain ⟨hc, _, hd⟩ := edf_prefix_well_formedness sched hmust hcde hdm horizon
  exact scheduled_at_implies_later_deadline _ hc j t (hd j t hs) hs

/-- Jobs scheduled in the EDF prefix are scheduled somewhere originally. -/
theorem edf_prefix_job_scheduled [JobDeadline Job] [JobArrival Job] (sched : schedule (processor_state Job))
    (horizon : instant) (j : Job) (t : instant) :
    scheduled_at (edf_transform_prefix sched horizon) j t = true → ∃ t' : instant, scheduled_at sched j t' = true := by
  revert t
  unfold edf_transform_prefix
  apply prefix_map_property_invariance (fun s => ∀ t, scheduled_at s j t = true → ∃ t', scheduled_at sched j t' = true)
  · intro s tr hp t hs
    obtain ⟨t1, ht1⟩ := mea_job_scheduled s tr j t hs
    exact hp t1 ht1
  · intro t hs; exact ⟨t, hs⟩

/-- Jobs scheduled originally are scheduled somewhere in the EDF prefix. -/
theorem edf_prefix_job_scheduled' [JobDeadline Job] [JobArrival Job] (sched : schedule (processor_state Job))
    (horizon : instant) (j : Job) (t : instant) :
    scheduled_at sched j t = true → ∃ t' : instant, scheduled_at (edf_transform_prefix sched horizon) j t' = true := by
  intro hs
  unfold edf_transform_prefix
  apply prefix_map_property_invariance (fun s => ∃ t', scheduled_at s j t' = true)
  · intro s tr ⟨t1, ht1⟩
    exact mea_job_scheduled' s tr j t1 ht1
  · exact ⟨t, hs⟩

/-- The EDF prefix transformation preserves that jobs come from the arrival sequence. -/
theorem edf_prefix_jobs_come_from_arrival_sequence [JobDeadline Job] [JobArrival Job]
    (sched : schedule (processor_state Job)) (horizon : instant) (arr_seq : arrival_sequence Job) :
    jobs_come_from_arrival_sequence sched arr_seq →
      jobs_come_from_arrival_sequence (edf_transform_prefix sched horizon) arr_seq := by
  intro hfrom
  unfold edf_transform_prefix
  apply prefix_map_property_invariance (fun s => jobs_come_from_arrival_sequence s arr_seq)
  · intro s tr hs; exact mea_jobs_come_from_arrival_sequence s tr arr_seq hs
  · exact hfrom

/-- The EDF prefix transformation ensures `EDF_at` before the horizon. -/
theorem edf_prefix_guarantee [JobCost Job] [JobDeadline Job] [JobArrival Job]
    (sched : schedule (processor_state Job)) :
    jobs_must_arrive_to_execute sched → completed_jobs_dont_execute sched → all_deadlines_met sched →
      ∀ (horizon : instant) (t : Nat), t < horizon → EDF_at (edf_transform_prefix sched horizon) t := by
  intro hmust hcde hdm horizon t hlt
  unfold edf_transform_prefix
  exact prefix_map_pointwise_property
    (fun s => completed_jobs_dont_execute s ∧ jobs_must_arrive_to_execute s ∧ all_deadlines_met s)
    EDF_at make_edf_at
    (fun s tr ⟨hc, hm, hd⟩ =>
      ⟨mea_completed_jobs s hm hc hd tr, mea_jobs_must_arrive s hm hc hd tr, mea_no_deadline_misses s hm hc hd tr⟩)
    (fun s tr ⟨hc, hm, hd⟩ hpre => mea_EDF_widen s hm hc hd tr hpre)
    sched horizon ⟨hcde, hmust, hdm⟩ t hlt

end EDFPrefixFacts

section EDFPrefixInclusion

variable {Job : JobType} [DecidableEq Job]

/-- The EDF prefix transformation is prefix-stable. -/
theorem edf_prefix_inclusion [JobCost Job] [JobDeadline Job] [JobArrival Job]
    (sched : schedule (processor_state Job)) :
    jobs_must_arrive_to_execute sched → completed_jobs_dont_execute sched → all_deadlines_met sched →
      ∀ h1 h2 : Nat, h1 ≤ h2 →
        identical_prefix (edf_transform_prefix sched h1) (edf_transform_prefix sched h2) h1 := by
  intro hmust hcde hdm h1 h2 hle t ht
  induction h2 with
  | zero => omega'
  | succ h2 ih =>
    rcases Nat.lt_or_eq_of_le hle with hlt | heq
    · have hle' : h1 ≤ h2 := by omega'
      rw [ih hle']
      show edf_transform_prefix sched h2 t = make_edf_at (edf_transform_prefix sched h2) h2 t
      cases hst : edf_transform_prefix sched h2 h2 with
      | none =>
        have hsw : make_edf_at (edf_transform_prefix sched h2) h2 = edf_transform_prefix sched h2 := by
          unfold make_edf_at; rw [hst]
        rw [hsw]
      | some j =>
        have hsw : make_edf_at (edf_transform_prefix sched h2) h2 =
            swapped (edf_transform_prefix sched h2) h2
              (find_swap_candidate (edf_transform_prefix sched h2) h2 j) := by
          unfold make_edf_at; rw [hst]
        rw [hsw]
        have hsj := scheduled_of_sched _ j h2 hst
        exact swap_before_invariant _ h2 _
          (fsc_range1 _ (edf_prefix_jobs_must_arrive sched hmust hcde hdm h2) j h2 hsj
            (edf_prefix_scheduled_job_has_later_deadline sched hmust hcde hdm h2 j h2 hsj)) t (by omega')
    · subst heq; rfl

end EDFPrefixInclusion

section EDFTransformFacts

variable {Job : JobType} [DecidableEq Job]

/-- The EDF schedule agrees with every finite EDF prefix below its horizon. -/
theorem edf_finite_prefix [JobCost Job] [JobDeadline Job] [JobArrival Job] (sched : schedule (processor_state Job)) :
    jobs_must_arrive_to_execute sched → completed_jobs_dont_execute sched → all_deadlines_met sched →
      ∀ h : instant, identical_prefix (edf_transform sched) (edf_transform_prefix sched h) h := by
  intro hmust hcde hdm h t ht
  exact edf_prefix_inclusion sched hmust hcde hdm (t + 1) h (by omega') t (by omega')

/-- The transformation yields an EDF schedule. -/
theorem edf_transform_ensures_edf [JobCost Job] [JobDeadline Job] [JobArrival Job]
    (sched : schedule (processor_state Job)) :
    jobs_must_arrive_to_execute sched → completed_jobs_dont_execute sched → all_deadlines_met sched →
      EDF_schedule (edf_transform sched) := by
  intro hmust hcde hdm t j hsj t' j' hle hsj' harr
  have hid := edf_finite_prefix sched hmust hcde hdm (t' + 1)
  have hedf := edf_prefix_guarantee sched hmust hcde hdm (t' + 1) t (by omega')
  rw [identical_prefix_scheduled_at _ _ (t' + 1) hid j t (by omega')] at hsj
  rw [identical_prefix_scheduled_at _ _ (t' + 1) hid j' t' (by omega')] at hsj'
  exact hedf j hsj t' j' hle hsj' harr

/-- Completed jobs do not execute in the EDF schedule. -/
theorem edf_transform_completed_jobs_dont_execute [JobCost Job] [JobDeadline Job] [JobArrival Job]
    (sched : schedule (processor_state Job)) :
    jobs_must_arrive_to_execute sched → completed_jobs_dont_execute sched → all_deadlines_met sched →
      completed_jobs_dont_execute (edf_transform sched) := by
  intro hmust hcde hdm j t hs
  have hid := edf_finite_prefix sched hmust hcde hdm (t + 1)
  rw [identical_prefix_scheduled_at _ _ (t + 1) hid j t (by omega')] at hs
  rw [identical_prefix_service _ _ t (identical_prefix_inclusion _ _ (t + 1) t (by omega') hid) j]
  exact (edf_prefix_well_formedness sched hmust hcde hdm (t + 1)).1 j t hs

/-- Jobs must arrive to execute in the EDF schedule. -/
theorem edf_transform_jobs_must_arrive [JobCost Job] [JobDeadline Job] [JobArrival Job]
    (sched : schedule (processor_state Job)) :
    jobs_must_arrive_to_execute sched → completed_jobs_dont_execute sched → all_deadlines_met sched →
      jobs_must_arrive_to_execute (edf_transform sched) := by
  intro hmust hcde hdm j t hs
  exact (edf_prefix_well_formedness sched hmust hcde hdm (t + 1)).2.1 j t hs

/-- No scheduled job misses a deadline in the EDF schedule. -/
theorem edf_transform_deadlines_met [JobCost Job] [JobDeadline Job] [JobArrival Job]
    (sched : schedule (processor_state Job)) :
    jobs_must_arrive_to_execute sched → completed_jobs_dont_execute sched → all_deadlines_met sched →
      all_deadlines_met (edf_transform sched) := by
  intro hmust hcde hdm j t hs
  have hdl : t < job_deadline j :=
    edf_prefix_scheduled_job_has_later_deadline sched hmust hcde hdm (t + 1) j t hs
  have hid := identical_prefix_inclusion _ _ (job_deadline j + 1) (job_deadline j) (by omega')
    (edf_finite_prefix sched hmust hcde hdm (job_deadline j + 1))
  unfold job_meets_deadline
  rw [identical_prefix_completed_by _ _ (job_deadline j) hid j (job_deadline j) (Nat.le_refl _)]
  rw [identical_prefix_scheduled_at _ _ (job_deadline j) hid j t hdl] at hs
  exact (edf_prefix_well_formedness sched hmust hcde hdm (job_deadline j + 1)).2.2 j t hs

/-- Jobs scheduled in the EDF schedule are scheduled somewhere originally. -/
theorem edf_transform_job_scheduled [JobDeadline Job] [JobArrival Job] (sched : schedule (processor_state Job))
    (j : Job) (t : instant) :
    scheduled_at (edf_transform sched) j t = true → ∃ t' : instant, scheduled_at sched j t' = true := by
  intro hs
  exact edf_prefix_job_scheduled sched (t + 1) j t hs

/-- Jobs scheduled originally are scheduled somewhere in the EDF schedule. -/
theorem edf_transform_job_scheduled' [JobCost Job] [JobDeadline Job] [JobArrival Job]
    (sched : schedule (processor_state Job)) :
    jobs_must_arrive_to_execute sched → completed_jobs_dont_execute sched → all_deadlines_met sched →
      ∀ (j : Job) (t : instant), scheduled_at sched j t = true →
        ∃ t' : instant, scheduled_at (edf_transform sched) j t' = true := by
  intro hmust hcde hdm j t hs
  obtain ⟨t', ht'⟩ := edf_prefix_job_scheduled' sched (job_deadline j) j t hs
  have hdl := edf_prefix_scheduled_job_has_later_deadline sched hmust hcde hdm (job_deadline j) j t' ht'
  refine ⟨t', ?_⟩
  have heq := edf_prefix_inclusion sched hmust hcde hdm (t' + 1) (job_deadline j) (by omega') t' (by omega')
  show scheduled_at (edf_transform_prefix sched (t' + 1)) j t' = true
  rw [scheduled_at_def] at ht' ⊢
  rw [heq]
  exact ht'

/-- The EDF schedule preserves that jobs come from the arrival sequence. -/
theorem edf_transform_jobs_come_from_arrival_sequence [JobDeadline Job] [JobArrival Job]
    (sched : schedule (processor_state Job)) (arr_seq : arrival_sequence Job) :
    jobs_come_from_arrival_sequence sched arr_seq → jobs_come_from_arrival_sequence (edf_transform sched) arr_seq := by
  intro hfrom j t hs
  exact edf_prefix_jobs_come_from_arrival_sequence sched (t + 1) arr_seq hfrom j t hs

end EDFTransformFacts

section Optimality

variable {Job : JobType} [DecidableEq Job]

/-- The EDF schedule is valid. -/
theorem edf_schedule_is_valid [JobCost Job] [JobDeadline Job] [JobArrival Job] (arr_seq : arrival_sequence Job)
    (sched : schedule (processor_state Job)) :
    @valid_schedule Job _ _ (processor_state Job) sched _ basic_ready_instance arr_seq →
      all_deadlines_met sched →
      @valid_schedule Job _ _ (processor_state Job) (edf_transform sched) _ basic_ready_instance arr_seq := by
  intro hvs hdm
  have hmust := @jobs_must_arrive_to_be_ready Job _ _ sched _ _ basic_ready_instance hvs.2
  have hcde := @completed_jobs_are_not_ready Job _ _ sched _ _ basic_ready_instance hvs.2
  exact ⟨edf_transform_jobs_come_from_arrival_sequence sched arr_seq hvs.1,
    basic_readiness_compliance _ (edf_transform_jobs_must_arrive sched hmust hcde hdm)
      (edf_transform_completed_jobs_dont_execute sched hmust hcde hdm)⟩

/-- The EDF schedule meets all deadlines. -/
theorem edf_schedule_meets_all_deadlines [JobCost Job] [JobDeadline Job] [JobArrival Job]
    (arr_seq : arrival_sequence Job) (sched : schedule (processor_state Job)) :
    @valid_schedule Job _ _ (processor_state Job) sched _ basic_ready_instance arr_seq →
      all_deadlines_met sched → all_deadlines_met (edf_transform sched) := by
  intro hvs hdm
  exact edf_transform_deadlines_met sched (@jobs_must_arrive_to_be_ready Job _ _ sched _ _ basic_ready_instance hvs.2)
    (@completed_jobs_are_not_ready Job _ _ sched _ _ basic_ready_instance hvs.2) hdm

/-- The EDF schedule meets the deadlines of all arriving jobs. -/
theorem edf_schedule_meets_all_deadlines_wrt_arrivals [JobCost Job] [JobDeadline Job] [JobArrival Job]
    (arr_seq : arrival_sequence Job) (sched : schedule (processor_state Job)) :
    @valid_schedule Job _ _ (processor_state Job) sched _ basic_ready_instance arr_seq →
      all_deadlines_of_arrivals_met arr_seq sched → all_deadlines_of_arrivals_met arr_seq (edf_transform sched) := by
  intro hvs hdoa j harr
  have hmust := @jobs_must_arrive_to_be_ready Job _ _ sched _ _ basic_ready_instance hvs.2
  have hcde := @completed_jobs_are_not_ready Job _ _ sched _ _ basic_ready_instance hvs.2
  by_cases hc : job_cost j = 0
  · unfold job_meets_deadline completed_by
    rw [hc]; exact decide_eq_true (Nat.zero_le _)
  · have hcomp := hdoa j harr
    unfold job_meets_deadline at hcomp
    obtain ⟨t', _, hs'⟩ := completed_implies_scheduled_before sched j (Nat.pos_of_ne_zero hc) hmust _ hcomp
    have hnm := all_deadlines_met_in_valid_schedule arr_seq sched hvs.1 hdoa
    obtain ⟨t'', hs''⟩ := edf_transform_job_scheduled' sched hmust hcde hnm j t' hs'
    exact edf_schedule_meets_all_deadlines arr_seq sched hvs hnm j t'' hs''

end Optimality

end Prosa.Analysis.Facts.Transform.EdfOpt
