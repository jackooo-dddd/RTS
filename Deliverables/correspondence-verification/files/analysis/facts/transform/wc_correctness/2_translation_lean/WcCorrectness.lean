-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/facts/transform/wc_correctness.v

import Prosa.Analysis.Transform.WcTrans
import Prosa.Analysis.Facts.Transform.Swaps
import Prosa.Analysis.Facts.Model.Ideal.Schedule
import Prosa.Analysis.Definitions.Schedulability
import Prosa.Analysis.Facts.Behavior.Arrivals
import Prosa.Analysis.Facts.Behavior.Completion
import Prosa.Analysis.Facts.Behavior.Service
import Prosa.Model.Readiness.Basic
import Prosa.Model.Schedule.WorkConserving

namespace Prosa.Analysis.Facts.Transform.WcCorrectness

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Ready
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Behavior.Time
open Prosa.Model.Processor.Ideal
open Prosa.Model.Processor.PlatformProperties
open Prosa.Model.Readiness.Basic
open Prosa.Model.Schedule.WorkConserving
open Prosa.Util.SearchArg
open Prosa.Util.List
open Prosa.Analysis.Transform.Swap
open Prosa.Analysis.Transform.Prefix
open Prosa.Analysis.Transform.WcTrans
open Prosa.Analysis.Definitions.Schedulability
open Prosa.Analysis.Facts.Transform.Swaps
open Prosa.Analysis.Facts.Model.Ideal.Schedule
open Prosa.Analysis.Facts.Behavior.Arrivals
open Prosa.Analysis.Facts.Behavior.Completion
open Prosa.Analysis.Facts.Behavior.Service

/-! Correctness of the work-conservation transformation.

Binder orders and hypothesis sets follow the elaborated source types (unused section context and hypotheses are
absent; the doubled deadline hypothesis of `mwa_finds_ready_jobs` is kept). The processor model is the accepted
ideal uniprocessor `processor_state Job`; the source's `#[local] Existing Instance basic_ready_instance` is the
accepted Lean definition `basic_ready_instance`, registered as a local instance, so readiness in the statements is
that instance, as in the elaborated types (`job_ready` is applied to it explicitly). A Boolean in `Prop` position is `= true`; `s == Some j` on processor
states is the equality `s = some j`; `t1 <= t < t2` is `(decide (t1 ≤ t) && decide (t < t2)) = true`. The
section-local `order` on naturals is applied, as in the elaborated `search_result`, to the states coerced to
naturals through `isSome` (`Bool.toNat`). -/

/-- `omega` after unfolding the time aliases. -/
macro "omega'" : tactic => `(tactic| (try dsimp only [instant, duration, work] at *) <;> omega)

section AuxiliaryLemmasWorkConservingTransformation

variable {Job : JobType} [DecidableEq Job]

attribute [local instance] basic_ready_instance

/-- Readiness under the basic model (the source's local instance). -/
local notation "bjr" => @job_ready _ _ _ _ _ basic_ready_instance

/-- Work conservation at `t`: the presence of a ready job implies that the processor is not idle. -/
def is_work_conserving_at [JobArrival Job] [JobCost Job] (arr_seq : arrival_sequence Job)
    (sched : schedule (processor_state Job)) (t : instant) : Prop :=
  (∃ j, arrives_in arr_seq j ∧ bjr sched j t = true) → ∃ j, sched t = some j

/-- The constant-false ordering of the search. -/
def order (_ _ : Nat) : Bool := false

/-- The result of the search for a swap candidate. -/
def search_result [JobArrival Job] [JobDeadline Job] (arr_seq : arrival_sequence Job)
    (sched : schedule (processor_state Job)) (t : instant) : Option Nat :=
  let max_dl := max_deadline_for_jobs_arrived_before arr_seq t
  search_arg sched (relevant_pstate t) (fun x y => order (Bool.toNat x.isSome) (Bool.toNat y.isSome)) t max_dl

private theorem sched_of_scheduled (sched : schedule (processor_state Job)) (j : Job) (t : instant)
    (h : scheduled_at sched j t = true) : sched t = some j := by
  rw [scheduled_at_def] at h; simpa using h

private theorem scheduled_of_sched (sched : schedule (processor_state Job)) (j : Job) (t : instant)
    (h : sched t = some j) : scheduled_at sched j t = true := by
  rw [scheduled_at_def]; simpa using h

private theorem swapped_at_t1 (sched : schedule (processor_state Job)) (t1 t2 : instant) :
    swapped sched t1 t2 t1 = sched t2 := by
  unfold swapped replace_at
  by_cases h : t2 = t1
  · subst h; simp
  · simp [h]

private theorem swapped_other (sched : schedule (processor_state Job)) (t1 t2 t : instant)
    (h1 : t ≠ t1) (h2 : t ≠ t2) : swapped sched t1 t2 t = sched t := by
  unfold swapped replace_at
  simp [Ne.symm h1, Ne.symm h2]

private theorem service_at_none (sched : schedule (processor_state Job)) (j : Job) (t : instant)
    (h : sched t = none) : service_at sched j t = 0 := by
  rw [service_at_def, h]; simp

private theorem ready_basic [JobArrival Job] [JobCost Job] (sched : schedule (processor_state Job)) (j : Job)
    (t : instant) : bjr sched j t = pending sched j t := rfl

/-- The search result is the search of `find_swap_candidate`. -/
private theorem search_result_eq [JobArrival Job] [JobDeadline Job] (arr_seq : arrival_sequence Job)
    (sched : schedule (processor_state Job)) (t : instant) :
    search_result arr_seq sched t =
      search_arg sched (relevant_pstate t) (fun _ _ => false) t (max_deadline_for_jobs_arrived_before arr_seq t) :=
  rfl

private theorem fsc_of_search [JobArrival Job] [JobDeadline Job] (arr_seq : arrival_sequence Job)
    (sched : schedule (processor_state Job)) (t : instant) :
    find_swap_candidate arr_seq sched t =
      match search_result arr_seq sched t with
      | some t_swap => t_swap
      | none => t :=
  rfl

/-- The swap candidate is not earlier than the reference time. -/
theorem swap_candidate_is_in_future [JobArrival Job] [JobDeadline Job] (arr_seq : arrival_sequence Job)
    (sched : schedule (processor_state Job)) (t1 : instant) :
    t1 ≤ find_swap_candidate arr_seq sched t1 := by
  rw [fsc_of_search]
  cases h : search_result arr_seq sched t1 with
  | none => exact Nat.le_refl _
  | some n => exact (search_arg_in_range _ _ _ _ _ _ h).1

/-- The job found by the search has arrived by the reference time. -/
theorem fsc_respects_has_arrived [JobArrival Job] [JobCost Job] [JobDeadline Job] (arr_seq : arrival_sequence Job)
    (sched : schedule (processor_state Job)) :
    jobs_must_be_ready_to_execute sched →
      ∀ (j : Job) (t : instant), sched (find_swap_candidate arr_seq sched t) = some j → has_arrived j t = true := by
  intro hready j t hs
  rw [fsc_of_search] at hs
  cases h : search_result arr_seq sched t with
  | none =>
    rw [h] at hs
    exact ready_implies_arrived sched j t (hready j t (scheduled_of_sched sched j t hs))
  | some n =>
    rw [h] at hs
    have hp := search_arg_pred _ _ _ _ _ _ h
    rw [hs] at hp
    exact hp

/-- Jobs arrive before they execute in the swapped schedule. -/
theorem swap_jobs_must_arrive_to_execute [JobArrival Job] [JobCost Job] [JobDeadline Job]
    (arr_seq : arrival_sequence Job) (sched : schedule (processor_state Job)) :
    jobs_must_be_ready_to_execute sched →
      ∀ t1 : instant, jobs_must_arrive_to_execute (swapped sched t1 (find_swap_candidate arr_seq sched t1)) := by
  intro hready t1 j t hs
  have hord := swap_candidate_is_in_future arr_seq sched t1
  rcases swap_job_scheduled_cases sched t1 _ j t hs with hc | ⟨ht, hc⟩ | ⟨ht, hc⟩
  · rw [hc] at hs
    exact ready_implies_arrived sched j t (hready j t hs)
  · rw [hc] at hs
    subst ht
    exact fsc_respects_has_arrived arr_seq sched hready j t (sched_of_scheduled sched j _ hs)
  · rw [hc] at hs
    have ha := of_decide_eq_true (ready_implies_arrived sched j t1 (hready j t1 hs))
    subst ht
    exact decide_eq_true (Nat.le_trans ha hord)

/-- Jobs are ready when scheduled in the swapped schedule. -/
theorem fsc_jobs_must_be_ready_to_execute [JobArrival Job] [JobCost Job] [JobDeadline Job]
    (arr_seq : arrival_sequence Job) (sched : schedule (processor_state Job)) :
    jobs_must_be_ready_to_execute sched →
      ∀ t1 : instant, jobs_must_be_ready_to_execute (swapped sched t1 (find_swap_candidate arr_seq sched t1)) := by
  intro hready t1 j t hs
  have harr := swap_jobs_must_arrive_to_execute arr_seq sched hready t1 j t hs
  have hcde := swapped_completed_jobs_dont_execute sched t1 _ (swap_candidate_is_in_future arr_seq sched t1)
    (ideal_proc_model_provides_unit_service Job) (ideal_proc_model_ensures_ideal_progress Job)
    (completed_jobs_are_not_ready sched hready) j t hs
  rw [ready_basic]
  unfold pending completed_by
  rw [harr]
  simp only [Bool.true_and, Bool.not_eq_true', decide_eq_false_iff_not, Nat.not_le]
  exact hcde

/-- The point-wise transformation only increases service. -/
theorem mwa_service_bound [JobArrival Job] [JobDeadline Job] (arr_seq : arrival_sequence Job)
    (sched : schedule (processor_state Job)) (t : instant) (j : Job) (t0 : instant) :
    service sched j t0 ≤ service (make_wc_at arr_seq sched t) j t0 := by
  unfold make_wc_at
  cases h : sched t with
  | some _ => exact Nat.le_refl _
  | none =>
    dsimp only
    have hord := swap_candidate_is_in_future arr_seq sched t
    by_cases hlt : find_swap_candidate arr_seq sched t < t0
    · rw [service_after_swap_invariant sched t _ hord t0 hlt j]
    · unfold service service_during
      apply Finset.sum_le_sum
      intro x hx
      rw [Finset.mem_Ico] at hx
      by_cases hxt : x = t
      · subst hxt
        rw [service_at_none sched j x h]
        exact Nat.zero_le _
      · have hx2 : x ≠ find_swap_candidate arr_seq sched t := by omega'
        unfold service_at
        rw [swapped_other sched t _ x hxt hx2]

/-- A job ready after the point-wise transformation is ready in the original schedule. -/
theorem mwa_ready_job_also_ready_in_original_schedule [JobArrival Job] [JobCost Job] [JobDeadline Job]
    (arr_seq : arrival_sequence Job) (sched : schedule (processor_state Job)) (t : instant) (j : Job)
    (t0 : instant) :
    bjr (make_wc_at arr_seq sched t) j t0 = true → bjr sched j t0 = true := by
  rw [ready_basic, ready_basic]
  unfold pending completed_by
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, Nat.not_le]
  intro ⟨ha, hc⟩
  exact ⟨ha, Nat.lt_of_le_of_lt (mwa_service_bound arr_seq sched t j t0) hc⟩

/-- The maximal deadline bounds the deadline of every arrived job. -/
theorem max_dl_is_greatest_dl [JobArrival Job] [JobDeadline Job] (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
      ∀ (j : Job) (t : Nat), arrives_in arr_seq j → job_arrival j ≤ t →
        job_deadline j ≤ max_deadline_for_jobs_arrived_before arr_seq t := by
  intro hva j t harr hle
  unfold max_deadline_for_jobs_arrived_before
  apply in_max0_le
  apply List.mem_map_of_mem
  have := arrived_between_implies_in_arrivals arr_seq hva.1 j 0 (t + 1) harr
    (by unfold arrived_between; simp only [Bool.and_eq_true, decide_eq_true_eq]; omega')
  exact of_decide_eq_true this

/-- A found swap candidate yields a scheduled job at the idle instant. -/
theorem make_wc_at_case_result_found [JobArrival Job] [JobDeadline Job] (arr_seq : arrival_sequence Job)
    (sched : schedule (processor_state Job)) (t : instant) :
    ideal_is_idle sched t = true →
      ∀ t_swap : instant, search_result arr_seq sched t = some t_swap →
        ∃ j : Job, swapped sched t t_swap t = some j := by
  intro _ t_swap h
  have hp := search_arg_pred _ _ _ _ _ _ h
  rw [swapped_at_t1]
  cases hs : sched t_swap with
  | none => rw [hs] at hp; simp [relevant_pstate] at hp
  | some j => exact ⟨j, rfl⟩

/-- Without a search result, no relevant state lies in the search window. -/
theorem no_relevant_state_in_range [JobArrival Job] [JobDeadline Job] (arr_seq : arrival_sequence Job)
    (sched : schedule (processor_state Job)) (t : instant) :
    search_result arr_seq sched t = none →
      ∀ t' : Nat, (decide (t ≤ t') && decide (t' < max_deadline_for_jobs_arrived_before arr_seq t)) = true →
        (!relevant_pstate t (sched t')) = true := by
  intro h t' hr
  have := (search_arg_none _ _ _ _ _).1 h t' (by simpa using hr)
  simp [this]

/-- A job ready after the point-wise transformation is incomplete in the original schedule. -/
theorem service_of_j_is_less_than_cost [JobArrival Job] [JobCost Job] [JobDeadline Job]
    (arr_seq : arrival_sequence Job) (sched : schedule (processor_state Job)) (t : instant) (j : Job) :
    bjr (make_wc_at arr_seq sched t) j t = true → service sched j t < job_cost j := by
  intro hr
  have h := mwa_ready_job_also_ready_in_original_schedule arr_seq sched t j t hr
  rw [ready_basic] at h
  unfold pending completed_by at h
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, Nat.not_le] at h
  exact h.2

/-- The deadline of such a job is not earlier than `t`. -/
theorem t_is_less_than_deadline_of_j [JobArrival Job] [JobCost Job] [JobDeadline Job]
    (arr_seq : arrival_sequence Job) (sched : schedule (processor_state Job)) (t : instant) :
    all_deadlines_of_arrivals_met arr_seq sched →
      ∀ j : Job, arrives_in arr_seq j → bjr (make_wc_at arr_seq sched t) j t = true → t ≤ job_deadline j := by
  intro hdoa j harr hr
  have hlt := service_of_j_is_less_than_cost arr_seq sched t j hr
  have hm := of_decide_eq_true (hdoa j harr)
  by_contra hne
  have := service_monotonic sched j (job_deadline j) t (by omega')
  omega'

/-- Without a search result, the job receives no service between `t` and the maximal deadline. -/
theorem equal_service_t_max_dl [JobArrival Job] [JobCost Job] [JobDeadline Job] (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
      ∀ (sched : schedule (processor_state Job)) (t : instant), all_deadlines_of_arrivals_met arr_seq sched →
        ∀ j : Job, arrives_in arr_seq j → bjr (make_wc_at arr_seq sched t) j t = true →
          search_result arr_seq sched t = none →
            service sched j t = service sched j (max_deadline_for_jobs_arrived_before arr_seq t) := by
  intro hva sched t hdoa j harr hr hnone
  have hr' := hr
  rw [ready_basic] at hr'
  unfold pending at hr'
  simp only [Bool.and_eq_true] at hr'
  have ha := of_decide_eq_true hr'.1
  have hdl := t_is_less_than_deadline_of_j arr_seq sched t hdoa j harr hr
  have hmax := max_dl_is_greatest_dl arr_seq hva j t harr ha
  rw [← service_cat sched j t _ (Nat.le_trans hdl hmax)]
  have hz : service_during sched j t (max_deadline_for_jobs_arrived_before arr_seq t) = 0 := by
    apply not_scheduled_during_implies_zero_service
    intro t' hrange
    have hnr := no_relevant_state_in_range arr_seq sched t hnone t' hrange
    rw [scheduled_at_def]
    cases hs : sched t' with
    | none => simp
    | some j' =>
      by_cases hj : j' = j
      · subst hj
        rw [hs] at hnr
        simp [relevant_pstate] at hnr
        omega'
      · simp only [Bool.not_eq_true', decide_eq_false_iff_not]
        exact fun h => hj (Option.some.inj h)
  rw [hz, Nat.add_zero]

/-- Such a job misses its deadline. -/
theorem j_misses_deadline [JobArrival Job] [JobCost Job] [JobDeadline Job] (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
      ∀ (sched : schedule (processor_state Job)) (t : instant), all_deadlines_of_arrivals_met arr_seq sched →
        ∀ j : Job, arrives_in arr_seq j → bjr (make_wc_at arr_seq sched t) j t = true →
          search_result arr_seq sched t = none → service sched j (job_deadline j) < job_cost j := by
  intro hva sched t hdoa j harr hr hnone
  have hr' := hr
  rw [ready_basic] at hr'
  unfold pending at hr'
  simp only [Bool.and_eq_true] at hr'
  have ha := of_decide_eq_true hr'.1
  have hlt := service_of_j_is_less_than_cost arr_seq sched t j hr
  rw [equal_service_t_max_dl arr_seq hva sched t hdoa j harr hr hnone] at hlt
  exact Nat.lt_of_le_of_lt
    (service_monotonic sched j _ _ (max_dl_is_greatest_dl arr_seq hva j t harr ha)) hlt

/-- A missing search result contradicts the met deadlines. -/
theorem make_wc_at_case_result_none [JobArrival Job] [JobCost Job] [JobDeadline Job]
    (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
      ∀ (sched : schedule (processor_state Job)) (t : instant), all_deadlines_of_arrivals_met arr_seq sched →
        ∀ j : Job, arrives_in arr_seq j → bjr (make_wc_at arr_seq sched t) j t = true →
          search_result arr_seq sched t = none → False := by
  intro hva sched t hdoa j harr hr hnone
  have hm := of_decide_eq_true (hdoa j harr)
  have := j_misses_deadline arr_seq hva sched t hdoa j harr hr hnone
  omega'

/-- The point-wise transformation establishes work conservation at `t`. -/
theorem mwa_finds_ready_jobs [JobArrival Job] [JobCost Job] [JobDeadline Job] (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
      ∀ (sched : schedule (processor_state Job)) (t : instant), all_deadlines_of_arrivals_met arr_seq sched →
        all_deadlines_of_arrivals_met arr_seq sched → is_work_conserving_at arr_seq (make_wc_at arr_seq sched t) t := by
  intro hva sched t hdoa _ ⟨j, harr, hready⟩
  cases hst : sched t with
  | some j' =>
    refine ⟨j', ?_⟩
    unfold make_wc_at; rw [hst]; exact hst
  | none =>
    have hmwa : make_wc_at arr_seq sched t = swapped sched t (find_swap_candidate arr_seq sched t) := by
      unfold make_wc_at; rw [hst]
    cases hs : search_result arr_seq sched t with
    | some t_swap =>
      have hf : find_swap_candidate arr_seq sched t = t_swap := by rw [fsc_of_search, hs]
      rw [hmwa, hf]
      exact make_wc_at_case_result_found arr_seq sched t (by unfold ideal_is_idle; rw [hst]) t_swap hs
    | none => exact (make_wc_at_case_result_none arr_seq hva sched t hdoa j harr hready hs).elim

/-- The point-wise transformation extends work conservation up to `t`. -/
theorem mwa_establishes_wc [JobArrival Job] [JobCost Job] [JobDeadline Job] (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
      ∀ (sched : schedule (processor_state Job)) (t : instant), all_deadlines_of_arrivals_met arr_seq sched →
        (∀ t_l : Nat, t_l < t → is_work_conserving_at arr_seq sched t_l) →
          ∀ t_l : Nat, t_l ≤ t → is_work_conserving_at arr_seq (make_wc_at arr_seq sched t) t_l := by
  intro hva sched t hdoa hpre t_l hle ⟨j, harr, hready⟩
  rcases Nat.lt_or_eq_of_le hle with hlt | heq
  · have hsame : make_wc_at arr_seq sched t t_l = sched t_l := by
      unfold make_wc_at
      cases hst : sched t with
      | some _ => rfl
      | none =>
        dsimp only
        exact (swap_before_invariant sched t _ (swap_candidate_is_in_future arr_seq sched t) t_l hlt).symm
    rw [hsame]
    exact hpre t_l hlt ⟨j, harr, mwa_ready_job_also_ready_in_original_schedule arr_seq sched t j t_l hready⟩
  · subst heq
    exact mwa_finds_ready_jobs arr_seq hva sched t_l hdoa hdoa ⟨j, harr, hready⟩

/-- The point-wise transformation keeps jobs from the arrival sequence. -/
theorem mwa_jobs_come_from_arrival_sequence [JobArrival Job] [JobDeadline Job] (arr_seq : arrival_sequence Job)
    (sched : schedule (processor_state Job)) (t : instant) :
    jobs_come_from_arrival_sequence sched arr_seq →
      jobs_come_from_arrival_sequence (make_wc_at arr_seq sched t) arr_seq := by
  intro hfrom
  unfold make_wc_at
  cases sched t with
  | some _ => exact hfrom
  | none => exact swapped_jobs_come_from_arrival_sequence sched t _ arr_seq hfrom

/-- The point-wise transformation keeps jobs ready when scheduled. -/
theorem mwa_jobs_must_be_ready_to_execute [JobArrival Job] [JobCost Job] [JobDeadline Job]
    (arr_seq : arrival_sequence Job) (sched : schedule (processor_state Job)) (t : instant) :
    jobs_must_be_ready_to_execute sched → jobs_must_be_ready_to_execute (make_wc_at arr_seq sched t) := by
  intro hready
  unfold make_wc_at
  cases sched t with
  | some _ => exact hready
  | none => exact fsc_jobs_must_be_ready_to_execute arr_seq sched hready t

/-- The point-wise transformation introduces no deadline miss. -/
theorem mwa_all_deadlines_of_arrivals_met [JobArrival Job] [JobCost Job] [JobDeadline Job]
    (arr_seq : arrival_sequence Job) (sched : schedule (processor_state Job)) (t : instant) :
    all_deadlines_of_arrivals_met arr_seq sched → all_deadlines_of_arrivals_met arr_seq (make_wc_at arr_seq sched t) := by
  intro hdoa j harr
  have hm := of_decide_eq_true (hdoa j harr)
  unfold job_meets_deadline completed_by
  exact decide_eq_true (Nat.le_trans hm (mwa_service_bound arr_seq sched t j _))

/-- Transformation prefixes agree below the earlier horizon. -/
theorem wc_transform_prefix_inclusion [JobArrival Job] [JobDeadline Job] (arr_seq : arrival_sequence Job)
    (sched : schedule (processor_state Job)) (h1 h2 : instant) :
    h1 ≤ h2 → ∀ t : Nat, t < h1 → wc_transform_prefix arr_seq sched h1 t = wc_transform_prefix arr_seq sched h2 t := by
  intro hle t ht
  induction h2 with
  | zero => exact absurd (Nat.lt_of_lt_of_le ht hle) (Nat.not_lt_zero _)
  | succ h2 ih =>
    rcases Nat.lt_or_eq_of_le hle with hlt | heq
    · have hle' : h1 ≤ h2 := Nat.le_of_lt_succ hlt
      rw [ih hle']
      show wc_transform_prefix arr_seq sched h2 t = make_wc_at arr_seq (wc_transform_prefix arr_seq sched h2) h2 t
      have htl : t < h2 := Nat.lt_of_lt_of_le ht hle'
      unfold make_wc_at
      cases hc : wc_transform_prefix arr_seq sched h2 h2 with
      | none => exact swap_before_invariant _ h2 _ (swap_candidate_is_in_future arr_seq _ h2) t htl
      | some _ => rfl
    · subst heq; rfl

/-- The full transformation agrees with its finite prefixes below their horizons. -/
private theorem wc_transform_prefix_agree [JobArrival Job] [JobDeadline Job] (arr_seq : arrival_sequence Job)
    (sched : schedule (processor_state Job)) (h : instant) :
    ∀ x : Nat, x < h → wc_transform arr_seq sched x = wc_transform_prefix arr_seq sched h x := by
  intro x hx
  exact wc_transform_prefix_inclusion arr_seq sched (x + 1) h (by omega') x (by omega')

private theorem wc_transform_service_eq [JobArrival Job] [JobDeadline Job] (arr_seq : arrival_sequence Job)
    (sched : schedule (processor_state Job)) (j : Job) (t h : instant) (hth : t ≤ h) :
    service (wc_transform arr_seq sched) j t = service (wc_transform_prefix arr_seq sched h) j t := by
  unfold service
  apply equal_prefix_implies_same_service_during
  intro x hx
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hx
  exact wc_transform_prefix_agree arr_seq sched h x (by omega')

/-- The transformation only increases service. -/
theorem wc_prefix_service_bound [JobArrival Job] [JobDeadline Job] (arr_seq : arrival_sequence Job)
    (sched : schedule (processor_state Job)) (j : Job) (t : instant) :
    service sched j t ≤ service (wc_transform arr_seq sched) j t := by
  rw [wc_transform_service_eq arr_seq sched j t (t + 1) (by omega')]
  unfold wc_transform_prefix
  apply prefix_map_property_invariance (fun s => service sched j t ≤ service s j t)
  · intro s t' hs
    exact Nat.le_trans hs (mwa_service_bound arr_seq s t' j t)
  · exact Nat.le_refl _

/-- The transformation introduces no deadline miss. -/
theorem wc_prefix_job_meets_deadline [JobArrival Job] [JobCost Job] [JobDeadline Job]
    (arr_seq : arrival_sequence Job) (sched : schedule (processor_state Job)) :
    all_deadlines_of_arrivals_met arr_seq sched →
      ∀ j : Job, arrives_in arr_seq j → job_meets_deadline (wc_transform arr_seq sched) j = true := by
  intro hdoa j harr
  have hm := of_decide_eq_true (hdoa j harr)
  unfold job_meets_deadline completed_by
  exact decide_eq_true (Nat.le_trans hm (wc_prefix_service_bound arr_seq sched j _))

/-- Transformation prefixes keep jobs from the arrival sequence. -/
theorem wc_prefix_jobs_come_from_arrival_sequence [JobArrival Job] [JobDeadline Job]
    (arr_seq : arrival_sequence Job) (sched : schedule (processor_state Job)) (h : instant) :
    jobs_come_from_arrival_sequence sched arr_seq →
      jobs_come_from_arrival_sequence (wc_transform_prefix arr_seq sched h) arr_seq := by
  intro hfrom
  unfold wc_transform_prefix
  apply prefix_map_property_invariance (fun s => jobs_come_from_arrival_sequence s arr_seq)
  · intro s t hs; exact mwa_jobs_come_from_arrival_sequence arr_seq s t hs
  · exact hfrom

/-- Transformation prefixes keep jobs ready when scheduled. -/
theorem wc_prefix_jobs_must_be_ready_to_execute [JobArrival Job] [JobCost Job] [JobDeadline Job]
    (arr_seq : arrival_sequence Job) (sched : schedule (processor_state Job)) (h : instant) :
    jobs_must_be_ready_to_execute sched → jobs_must_be_ready_to_execute (wc_transform_prefix arr_seq sched h) := by
  intro hready
  unfold wc_transform_prefix
  apply prefix_map_property_invariance (fun s => jobs_must_be_ready_to_execute s)
  · intro s t hs; exact mwa_jobs_must_be_ready_to_execute arr_seq s t hs
  · exact hready

end AuxiliaryLemmasWorkConservingTransformation

section WorkConservingTransformation

variable {Job : JobType} [DecidableEq Job]

attribute [local instance] basic_ready_instance

/-- Readiness under the basic model (the source's local instance). -/
local notation "bjr" => @job_ready _ _ _ _ _ basic_ready_instance

private theorem wc_ready_eq [JobArrival Job] [JobCost Job] [JobDeadline Job] (arr_seq : arrival_sequence Job)
    (sched : schedule (processor_state Job)) (j : Job) (t : instant) :
    bjr (wc_transform arr_seq sched) j t = bjr (wc_transform_prefix arr_seq sched (t + 1)) j t := by
  show pending _ j t = pending _ j t
  unfold pending completed_by
  rw [wc_transform_service_eq arr_seq sched j t (t + 1) (by omega')]

/-- Jobs of the transformed schedule come from the arrival sequence. -/
theorem wc_jobs_come_from_arrival_sequence [JobArrival Job] [JobCost Job] [JobDeadline Job]
    (arr_seq : arrival_sequence Job) (sched : schedule (processor_state Job)) :
    valid_schedule sched arr_seq → jobs_come_from_arrival_sequence (wc_transform arr_seq sched) arr_seq := by
  intro hvs j t hs
  exact wc_prefix_jobs_come_from_arrival_sequence arr_seq sched (t + 1) hvs.1 j t hs

/-- Jobs of the transformed schedule are ready when scheduled. -/
theorem wc_jobs_must_be_ready_to_execute [JobArrival Job] [JobCost Job] [JobDeadline Job]
    (arr_seq : arrival_sequence Job) (sched : schedule (processor_state Job)) :
    valid_schedule sched arr_seq → jobs_must_be_ready_to_execute (wc_transform arr_seq sched) := by
  intro hvs j t hs
  rw [wc_ready_eq]
  exact wc_prefix_jobs_must_be_ready_to_execute arr_seq sched (t + 1) hvs.2 j t hs

/-- The transformed schedule meets the deadlines of all arriving jobs. -/
theorem wc_all_deadlines_of_arrivals_met [JobArrival Job] [JobCost Job] [JobDeadline Job]
    (arr_seq : arrival_sequence Job) (sched : schedule (processor_state Job)) :
    all_deadlines_of_arrivals_met arr_seq sched → all_deadlines_of_arrivals_met arr_seq (wc_transform arr_seq sched) := by
  intro hdoa j harr
  exact wc_prefix_job_meets_deadline arr_seq sched hdoa j harr

/-- The processor is not idle when an arrived job is ready. -/
theorem wc_is_work_conserving_at [JobArrival Job] [JobCost Job] [JobDeadline Job] (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
      ∀ sched : schedule (processor_state Job), all_deadlines_of_arrivals_met arr_seq sched →
        ∀ (j : Job) (t : instant), bjr (wc_transform arr_seq sched) j t = true → arrives_in arr_seq j →
          ∃ j' : Job, wc_transform arr_seq sched t = some j' := by
  intro hva sched hdoa j t hready harr
  have hq := prefix_map_pointwise_property (all_deadlines_of_arrivals_met arr_seq)
    (is_work_conserving_at arr_seq) (make_wc_at arr_seq)
    (fun s t' hs => mwa_all_deadlines_of_arrivals_met arr_seq s t' hs)
    (fun s t' hs hpre => mwa_establishes_wc arr_seq hva s t' hs hpre)
    sched (t + 1) hdoa t (by omega')
  rw [wc_ready_eq] at hready
  exact hq ⟨j, harr, hready⟩

/-- The transformed schedule is work-conserving. -/
theorem wc_is_work_conserving [JobArrival Job] [JobCost Job] [JobDeadline Job] (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
      ∀ sched : schedule (processor_state Job), all_deadlines_of_arrivals_met arr_seq sched →
        work_conserving arr_seq (wc_transform arr_seq sched) := by
  intro hva sched hdoa j t harr hback
  unfold backlogged at hback
  simp only [Bool.and_eq_true] at hback
  obtain ⟨j', hj'⟩ := wc_is_work_conserving_at arr_seq hva sched hdoa j t hback.1 harr
  exact ⟨j', scheduled_of_sched _ j' t hj'⟩

/-- The transformation keeps validity and met deadlines and establishes work conservation. -/
theorem wc_transform_correctness [JobArrival Job] [JobCost Job] [JobDeadline Job] (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
      ∀ sched : schedule (processor_state Job), valid_schedule sched arr_seq →
        all_deadlines_of_arrivals_met arr_seq sched →
          valid_schedule (wc_transform arr_seq sched) arr_seq ∧
            all_deadlines_of_arrivals_met arr_seq (wc_transform arr_seq sched) ∧
              work_conserving arr_seq (wc_transform arr_seq sched) := by
  intro hva sched hvs hdoa
  exact ⟨⟨wc_jobs_come_from_arrival_sequence arr_seq sched hvs, wc_jobs_must_be_ready_to_execute arr_seq sched hvs⟩,
    wc_all_deadlines_of_arrivals_met arr_seq sched hdoa, wc_is_work_conserving arr_seq hva sched hdoa⟩

end WorkConservingTransformation

end Prosa.Analysis.Facts.Transform.WcCorrectness
