-- Translated from: ../rt-proofs/analysis/facts/transform/edf_opt.v
import Prosa.Model.Schedule.Edf
import Prosa.Analysis.Definitions.Schedulability
import Prosa.Analysis.Transform.Edf_trans
import Prosa.Analysis.Facts.Transform.Swaps
import Prosa.Analysis.Facts.Readiness.Basic
import Prosa.Model.Processor.Ideal
import Prosa.Model.Readiness.Basic
import Prosa.Analysis.Facts.Model.Ideal_schedule
import Prosa.Analysis.Facts.Behavior.Deadlines
import Prosa.Analysis.Facts.Behavior.Completion

namespace Prosa.Analysis.Facts.Transform.Edf_opt

open Prosa.Behavior.Job
open Prosa.Behavior.Time
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Ready
open Prosa.Model.Processor.Ideal
open Prosa.Model.Schedule.Edf
open Prosa.Analysis.Definitions.Schedulability
open Prosa.Analysis.Transform.Edf_trans
open Prosa.Analysis.Transform.Prefix
open Prosa.Analysis.Transform.Swap
open Prosa.Analysis.Facts.Transform.Swaps
open Prosa.Analysis.Facts.Readiness.Basic
open Prosa.Analysis.Facts.Model.Ideal_schedule
open Prosa.Analysis.Facts.Behavior.Deadlines
open Prosa.Analysis.Facts.Behavior.Completion
open Prosa.Analysis.Facts.Behavior.Arrivals
open Prosa.Model.Processor.Platform_properties
open Prosa.Util.Search_arg

attribute [local instance] pstate_instance

/-! ## Intermediate lemmas for EDF optimality -/

-- Helper: unfold make_edf_at and case split
private theorem make_edf_at_none {Job : JobType} [JobCost Job] [JobDeadline Job] [JobArrival Job]
    [DecidableEq Job] (sched : schedule (processor_state Job)) (t_edf : instant)
    (h : sched t_edf = none) : make_edf_at sched t_edf = sched := by
  simp [make_edf_at, h]

private theorem make_edf_at_some {Job : JobType} [JobCost Job] [JobDeadline Job] [JobArrival Job]
    [DecidableEq Job] (sched : schedule (processor_state Job)) (t_edf : instant) (j_orig : Job)
    (h : sched t_edf = some j_orig) :
    make_edf_at sched t_edf = swapped sched t_edf (find_swap_candidate sched t_edf j_orig) := by
  simp [make_edf_at, h]

section FindSwapCandidateFacts

variable {Job : JobType} [JobCost Job] [JobDeadline Job] [JobArrival Job]
variable [DecidableEq Job]
variable (sched : schedule (processor_state Job))
variable (H_jobs_must_arrive : jobs_must_arrive_to_execute (Job := Job) sched)
variable (j1 : Job) (t1 : instant)
variable (H_not_idle : scheduled_at sched j1 t1 = true)
variable (H_deadline_not_missed : t1 < job_deadline j1)

include H_jobs_must_arrive H_not_idle H_deadline_not_missed in
theorem fsc_search_result :
    search_arg sched (relevant_pstate t1) (earlier_deadline (Job := Job)) t1 (job_deadline j1) =
    some (find_swap_candidate sched t1 j1) := by
  have h_eq : sched t1 = some j1 := by
    rw [scheduled_at_def] at H_not_idle; exact of_decide_eq_true H_not_idle
  have t1_rel : relevant_pstate t1 (sched t1) = true := by
    rw [h_eq]; simp only [relevant_pstate, decide_eq_true_eq]
    exact H_jobs_must_arrive j1 t1 H_not_idle
  have ⟨t, ht⟩ : ∃ t, search_arg sched (relevant_pstate t1) (earlier_deadline (Job := Job))
      t1 (job_deadline j1) = some t :=
    search_arg_not_none _ _ _ _ _ ⟨t1, ⟨Nat.le_refl t1, H_deadline_not_missed⟩, t1_rel⟩
  have : find_swap_candidate sched t1 j1 = t := by simp only [find_swap_candidate, ht]
  rw [this]; exact ht

include H_jobs_must_arrive H_not_idle H_deadline_not_missed in
theorem fsc_not_idle :
    ∃ (j' : Job), scheduled_at sched j' (find_swap_candidate sched t1 j1) = true ∧ job_arrival j' ≤ t1 := by
  have hpred : (relevant_pstate t1) (sched (find_swap_candidate sched t1 j1)) = true :=
    search_arg_pred sched (relevant_pstate t1) (earlier_deadline (Job := Job)) t1 (job_deadline j1)
      (find_swap_candidate sched t1 j1)
      (fsc_search_result sched H_jobs_must_arrive j1 t1 H_not_idle H_deadline_not_missed)
  cases h : sched (find_swap_candidate sched t1 j1) with
  | none => rw [h] at hpred; simp [relevant_pstate] at hpred
  | some j' =>
    refine ⟨j', ?_, ?_⟩
    · rw [scheduled_at_def]; exact decide_eq_true h
    · simp [relevant_pstate, h] at hpred; exact hpred

include H_jobs_must_arrive H_not_idle H_deadline_not_missed in
theorem fsc_found_job_arrival (j2 : Job)
    (h : scheduled_at sched j2 (find_swap_candidate sched t1 j1) = true) :
    job_arrival j2 ≤ t1 := by
  obtain ⟨j', sched_j', arr_j'⟩ := fsc_not_idle sched H_jobs_must_arrive j1 t1 H_not_idle H_deadline_not_missed
  rw [ideal_proc_model_is_a_uniprocessor_model j2 j' sched _ h sched_j']; exact arr_j'

include H_jobs_must_arrive H_not_idle H_deadline_not_missed in
theorem fsc_range :
    t1 ≤ find_swap_candidate sched t1 j1 ∧ find_swap_candidate sched t1 j1 < job_deadline j1 :=
  search_arg_in_range _ _ _ _ _ _
    (fsc_search_result sched H_jobs_must_arrive j1 t1 H_not_idle H_deadline_not_missed)

include H_jobs_must_arrive H_not_idle H_deadline_not_missed in
theorem fsc_range1 : t1 ≤ find_swap_candidate sched t1 j1 :=
  (fsc_range sched H_jobs_must_arrive j1 t1 H_not_idle H_deadline_not_missed).1

include H_jobs_must_arrive H_not_idle H_deadline_not_missed in
theorem fsc_found_job_deadline (j2 : Job)
    (H_sched_j2 : scheduled_at sched j2 (find_swap_candidate sched t1 j1) = true) :
    ∀ (j : Job) (t : instant),
      t1 ≤ t ∧ t < job_deadline j1 →
      scheduled_at sched j t = true →
      job_arrival j ≤ t1 →
      job_deadline j2 ≤ job_deadline j := by
  intro j t ⟨ht_lo, ht_hi⟩ sched_j arr_j
  have hres := fsc_search_result sched H_jobs_must_arrive j1 t1 H_not_idle H_deadline_not_missed
  have h_fsc : sched (find_swap_candidate sched t1 j1) = some j2 := by
    rw [scheduled_at_def] at H_sched_j2; exact of_decide_eq_true H_sched_j2
  have h_t : sched t = some j := by
    rw [scheduled_at_def] at sched_j; exact of_decide_eq_true sched_j
  have hrel : relevant_pstate t1 (sched t) = true := by
    rw [h_t]; simp [relevant_pstate, decide_eq_true_eq, arr_j]
  have hextr := search_arg_extremum sched (relevant_pstate t1) (earlier_deadline (Job := Job))
    (by intro x; simp [earlier_deadline])
    (by intro x y z h1 h2; simp only [earlier_deadline, decide_eq_true_eq] at *; exact Nat.le_trans h1 h2)
    (by intro x y; simp only [earlier_deadline, decide_eq_true_eq]; exact le_total _ _)
    t1 (job_deadline j1) (find_swap_candidate sched t1 j1) hres
  have hed := hextr t ⟨ht_lo, ht_hi⟩ hrel
  simp only [earlier_deadline, h_fsc, h_t, Option.elim, decide_eq_true_eq] at hed
  exact hed

include H_jobs_must_arrive H_not_idle H_deadline_not_missed in
theorem fsc_no_later_deadline (j2 : Job)
    (h : scheduled_at sched j2 (find_swap_candidate sched t1 j1) = true) :
    job_deadline j2 ≤ job_deadline j1 :=
  fsc_found_job_deadline sched H_jobs_must_arrive j1 t1 H_not_idle H_deadline_not_missed
    j2 h j1 t1 ⟨Nat.le_refl t1, H_deadline_not_missed⟩ H_not_idle
    (H_jobs_must_arrive j1 t1 H_not_idle)

end FindSwapCandidateFacts

/-! ## MakeEDFAtFacts -/

section MakeEDFAtFacts

variable {Job : JobType} [JobCost Job] [JobDeadline Job] [JobArrival Job]
variable [DecidableEq Job]
variable (sched : schedule (processor_state Job))
variable (H_jobs_must_arrive : jobs_must_arrive_to_execute (Job := Job) sched)
variable (H_completed_dont_execute : completed_jobs_dont_execute (Job := Job) sched)
variable (H_no_deadline_misses : all_deadlines_met (Job := Job) sched)
variable (t_edf : instant)

include H_completed_dont_execute H_no_deadline_misses in
private theorem sched_job_dl (j : Job) (t : instant)
    (h : scheduled_at sched j t = true) : t < job_deadline j :=
  scheduled_at_implies_later_deadline sched H_completed_dont_execute
    ideal_proc_model_ensures_ideal_progress j t (H_no_deadline_misses j t h) h

include H_jobs_must_arrive H_completed_dont_execute H_no_deadline_misses in
theorem mea_completed_jobs :
    completed_jobs_dont_execute (Job := Job) (make_edf_at sched t_edf) := by
  cases h : sched t_edf with
  | none => rw [make_edf_at_none _ _ h]; exact H_completed_dont_execute
  | some j_orig =>
    rw [make_edf_at_some _ _ _ h]
    have h_s := (by rw [scheduled_at_def]; exact decide_eq_true h : scheduled_at sched j_orig t_edf = true)
    exact swapped_completed_jobs_dont_execute sched t_edf (find_swap_candidate sched t_edf j_orig)
      (fsc_range1 sched H_jobs_must_arrive j_orig t_edf h_s (sched_job_dl sched H_completed_dont_execute H_no_deadline_misses j_orig t_edf h_s))
      ideal_proc_model_provides_unit_service
      ideal_proc_model_ensures_ideal_progress
      H_completed_dont_execute

include H_jobs_must_arrive H_completed_dont_execute H_no_deadline_misses in
theorem mea_no_deadline_misses :
    all_deadlines_met (Job := Job) (make_edf_at sched t_edf) := by
  intro j t sched_j
  cases h : sched t_edf with
  | none =>
    rw [make_edf_at_none _ _ h] at sched_j ⊢
    exact H_no_deadline_misses j t sched_j
  | some j_orig =>
    rw [make_edf_at_some _ _ _ h] at sched_j
    rw [make_edf_at_some sched t_edf j_orig h]
    have h_s : scheduled_at sched j_orig t_edf = true := by
      rw [scheduled_at_def]; exact decide_eq_true h
    have h_dl := sched_job_dl sched H_completed_dont_execute H_no_deadline_misses j_orig t_edf h_s
    have h_fsc_ge := fsc_range1 sched H_jobs_must_arrive j_orig t_edf h_s h_dl
    -- Get j scheduled in sched (hence meets deadline in sched)
    obtain ⟨t', ht'⟩ := swap_job_scheduled sched t_edf _ j t sched_j
    have dl_met := H_no_deadline_misses j t' ht'
    -- Build hypotheses for edf_swap_no_deadline_misses_introduced
    have H_not_EDF : ∀ (j1 j2 : Job),
        scheduled_at sched j1 t_edf = true →
        scheduled_at sched j2 (find_swap_candidate sched t_edf j_orig) = true →
        job_deadline j1 ≥ job_deadline j2 := by
      intro j1 j2 sj1 sj2
      rw [ideal_proc_model_is_a_uniprocessor_model j1 j_orig sched t_edf sj1 h_s]
      exact fsc_no_later_deadline sched H_jobs_must_arrive j_orig t_edf h_s h_dl j2 sj2
    have H_no_idle : ∀ (j1 : Job),
        scheduled_at sched j1 t_edf = true →
        ∃ (j2 : Job), scheduled_at sched j2 (find_swap_candidate sched t_edf j_orig) = true ∧
          job_deadline j2 > (find_swap_candidate sched t_edf j_orig) := by
      intro j1 _
      obtain ⟨j2, sj2, _⟩ := fsc_not_idle sched H_jobs_must_arrive j_orig t_edf h_s h_dl
      exact ⟨j2, sj2, sched_job_dl sched H_completed_dont_execute H_no_deadline_misses j2 _ sj2⟩
    exact edf_swap_no_deadline_misses_introduced sched H_completed_dont_execute
      ideal_proc_model_ensures_ideal_progress t_edf (find_swap_candidate sched t_edf j_orig)
      h_fsc_ge H_not_EDF H_no_idle j dl_met

-- mea_job_scheduled: NO include of hypotheses — only sched and t_edf are needed
theorem mea_job_scheduled (j : Job) (t : instant) :
    scheduled_at (make_edf_at sched t_edf) j t = true →
    ∃ t', scheduled_at sched j t' = true := by
  intro sched_j
  cases h : sched t_edf with
  | none => rw [make_edf_at_none _ _ h] at sched_j; exact ⟨t, sched_j⟩
  | some j_orig =>
    rw [make_edf_at_some _ _ _ h] at sched_j
    exact swap_job_scheduled sched t_edf _ j t sched_j

-- mea_job_scheduled': NO include of hypotheses
theorem mea_job_scheduled' (j : Job) (t : instant) :
    scheduled_at sched j t = true →
    ∃ t', scheduled_at (make_edf_at sched t_edf) j t' = true := by
  intro sched_j
  cases h : sched t_edf with
  | none => rw [make_edf_at_none _ _ h]; exact ⟨t, sched_j⟩
  | some j_orig =>
    rw [make_edf_at_some _ _ _ h]
    exact swap_job_scheduled_original sched t_edf _ j t sched_j

include H_jobs_must_arrive H_completed_dont_execute H_no_deadline_misses in
theorem mea_jobs_must_arrive :
    jobs_must_arrive_to_execute (Job := Job) (make_edf_at sched t_edf) := by
  intro j t sched_j
  cases h : sched t_edf with
  | none => rw [make_edf_at_none _ _ h] at sched_j; exact H_jobs_must_arrive j t sched_j
  | some j_orig =>
    rw [make_edf_at_some _ _ _ h] at sched_j
    have h_s : scheduled_at sched j_orig t_edf = true := by
      rw [scheduled_at_def]; exact decide_eq_true h
    have h_dl := sched_job_dl sched H_completed_dont_execute H_no_deadline_misses j_orig t_edf h_s
    have h_fsc_ge := fsc_range1 sched H_jobs_must_arrive j_orig t_edf h_s h_dl
    by_cases ht1 : t_edf = t
    · subst ht1
      suffices scheduled_at sched j (find_swap_candidate sched t_edf j_orig) = true by
        exact fsc_found_job_arrival sched H_jobs_must_arrive j_orig t_edf h_s h_dl j this
      rw [← swap_job_scheduled_t1 sched t_edf (find_swap_candidate sched t_edf j_orig) j]
      exact sched_j
    · by_cases ht2 : (find_swap_candidate sched t_edf j_orig) = t
      · subst ht2
        suffices scheduled_at sched j t_edf = true by
          exact Nat.le_trans (H_jobs_must_arrive j t_edf this) h_fsc_ge
        rw [← swap_job_scheduled_t2 sched t_edf (find_swap_candidate sched t_edf j_orig) j]
        exact sched_j
      · suffices scheduled_at sched j t = true by
          exact H_jobs_must_arrive j t this
        rw [← swap_job_scheduled_other_times sched t_edf
          (find_swap_candidate sched t_edf j_orig) j t ht1 ht2]
        exact sched_j

-- mea_jobs_come_from_arrival_sequence: minimal includes
section MeaArrivalSequence
variable (arr_seq : arrival_sequence Job)
variable (H_from_arr_seq : jobs_come_from_arrival_sequence sched arr_seq)

include H_from_arr_seq in
theorem mea_jobs_come_from_arrival_sequence :
    jobs_come_from_arrival_sequence (make_edf_at sched t_edf) arr_seq := by
  intro j t sched_j
  cases h : sched t_edf with
  | none => rw [make_edf_at_none _ _ h] at sched_j; exact H_from_arr_seq j t sched_j
  | some j_orig =>
    rw [make_edf_at_some _ _ _ h] at sched_j
    exact swapped_jobs_come_from_arrival_sequence sched t_edf _ arr_seq H_from_arr_seq j t sched_j
end MeaArrivalSequence

include H_jobs_must_arrive H_completed_dont_execute H_no_deadline_misses in
theorem make_edf_at_guarantee :
    EDF_at Job (processor_state Job) (make_edf_at sched t_edf) t_edf := by
  intro j_edf sched_j_edf t' j' ht' sched_j' arr_j'
  cases h : sched t_edf with
  | none =>
    rw [make_edf_at_none _ _ h, scheduled_at_def] at sched_j_edf
    simp [h] at sched_j_edf
  | some j_orig =>
    set fsc := find_swap_candidate sched t_edf j_orig
    have h_s : scheduled_at sched j_orig t_edf = true := by
      rw [scheduled_at_def]; exact decide_eq_true h
    have h_dl := sched_job_dl sched H_completed_dont_execute H_no_deadline_misses j_orig t_edf h_s
    rw [make_edf_at_some sched t_edf j_orig h] at sched_j_edf
    have fsc_sched : scheduled_at sched j_edf fsc = true := by
      suffices scheduled_at (swapped sched t_edf fsc) j_edf t_edf = scheduled_at sched j_edf fsc by
        rw [← this]; exact sched_j_edf
      exact swap_job_scheduled_t1 sched t_edf fsc j_edf
    have dl_bound : job_deadline j_edf ≤ job_deadline j_orig :=
      fsc_no_later_deadline sched H_jobs_must_arrive j_orig t_edf h_s h_dl j_edf fsc_sched
    by_cases hlt : t' < job_deadline j_orig
    · -- Before deadline: find j' in sched
      rw [make_edf_at_some sched t_edf j_orig h] at sched_j'
      rcases swap_job_scheduled_cases sched t_edf fsc j' t' sched_j' with h_eq | ⟨_, h_eq⟩ | ⟨_, h_eq⟩
      · have : scheduled_at sched j' t' = true := by rw [← h_eq]; exact sched_j'
        exact fsc_found_job_deadline sched H_jobs_must_arrive j_orig t_edf h_s h_dl
          j_edf fsc_sched j' t' ⟨ht', hlt⟩ this arr_j'
      · have : scheduled_at sched j' fsc = true := by rw [← h_eq]; exact sched_j'
        have ⟨lo, hi⟩ := fsc_range sched H_jobs_must_arrive j_orig t_edf h_s h_dl
        exact fsc_found_job_deadline sched H_jobs_must_arrive j_orig t_edf h_s h_dl
          j_edf fsc_sched j' fsc ⟨lo, hi⟩ this arr_j'
      · have : scheduled_at sched j' t_edf = true := by rw [← h_eq]; exact sched_j'
        exact fsc_found_job_deadline sched H_jobs_must_arrive j_orig t_edf h_s h_dl
          j_edf fsc_sched j' t_edf ⟨Nat.le_refl _, h_dl⟩ this arr_j'
    · -- Past deadline
      push_neg at hlt
      have mea_comp := mea_completed_jobs sched H_jobs_must_arrive H_completed_dont_execute H_no_deadline_misses t_edf
      have mea_dl := mea_no_deadline_misses sched H_jobs_must_arrive H_completed_dont_execute H_no_deadline_misses t_edf
      have dl_j' := scheduled_at_implies_later_deadline (make_edf_at sched t_edf) mea_comp
        ideal_proc_model_ensures_ideal_progress j' t' (mea_dl j' t' sched_j') sched_j'
      exact Nat.le_trans dl_bound (Nat.le_of_lt (Nat.lt_of_le_of_lt hlt dl_j'))

variable (H_EDF_prefix : ∀ t, t < t_edf → EDF_at Job (processor_state Job) sched t)

include H_jobs_must_arrive H_completed_dont_execute H_no_deadline_misses H_EDF_prefix in
theorem mea_EDF_widen :
    ∀ t, t ≤ t_edf → EDF_at Job (processor_state Job) (make_edf_at sched t_edf) t := by
  intro t ht
  rcases Nat.eq_or_lt_of_le ht with heq | hlt
  · subst heq
    exact make_edf_at_guarantee sched H_jobs_must_arrive H_completed_dont_execute H_no_deadline_misses _
  · cases h : sched t_edf with
    | none =>
      rw [make_edf_at_none _ _ h]
      exact H_EDF_prefix t hlt
    | some j_orig =>
      set fsc := find_swap_candidate sched t_edf j_orig
      have h_s : scheduled_at sched j_orig t_edf = true := by
        rw [scheduled_at_def]; exact decide_eq_true h
      have h_dl := sched_job_dl sched H_completed_dont_execute H_no_deadline_misses j_orig t_edf h_s
      have h_fsc_ge := fsc_range1 sched H_jobs_must_arrive j_orig t_edf h_s h_dl
      have h_lt_fsc : t < fsc := Nat.lt_of_lt_of_le hlt h_fsc_ge
      rw [make_edf_at_some sched t_edf j_orig h]
      intro j sched_j t' j' ht_le sched_j' arr_j'
      -- At time t < t_edf, swap doesn't change the schedule
      have sched_j_orig : scheduled_at sched j t = true := by
        suffices scheduled_at (swapped sched t_edf fsc) j t = scheduled_at sched j t by
          rw [← this]; exact sched_j
        exact swap_job_scheduled_other_times sched t_edf fsc j t
          (Nat.ne_of_gt hlt) (Nat.ne_of_gt h_lt_fsc)
      -- Find j' in original schedule via case analysis
      rcases swap_job_scheduled_cases sched t_edf fsc j' t' sched_j' with h_eq | ⟨_, h_eq⟩ | ⟨_, h_eq⟩
      · have : scheduled_at sched j' t' = true := by rw [← h_eq]; exact sched_j'
        exact H_EDF_prefix t hlt j sched_j_orig t' j' ht_le this arr_j'
      · have : scheduled_at sched j' fsc = true := by rw [← h_eq]; exact sched_j'
        exact H_EDF_prefix t hlt j sched_j_orig fsc j' (le_of_lt h_lt_fsc) this arr_j'
      · have : scheduled_at sched j' t_edf = true := by rw [← h_eq]; exact sched_j'
        exact H_EDF_prefix t hlt j sched_j_orig t_edf j' (le_of_lt hlt) this arr_j'

end MakeEDFAtFacts

/-! ## EDFPrefixFacts -/

section EDFPrefixFacts

variable {Job : JobType} [JobCost Job] [JobDeadline Job] [JobArrival Job]
variable [DecidableEq Job]
variable (sched : schedule (processor_state Job))
variable (H_jobs_must_arrive : jobs_must_arrive_to_execute (Job := Job) sched)
variable (H_completed_dont_execute : completed_jobs_dont_execute (Job := Job) sched)
variable (H_no_deadline_misses : all_deadlines_met (Job := Job) sched)
variable (horizon : instant)

include H_jobs_must_arrive H_completed_dont_execute H_no_deadline_misses in
theorem edf_prefix_well_formedness :
    completed_jobs_dont_execute (Job := Job) (edf_transform_prefix sched horizon) ∧
    jobs_must_arrive_to_execute (Job := Job) (edf_transform_prefix sched horizon) ∧
    all_deadlines_met (Job := Job) (edf_transform_prefix sched horizon) := by
  unfold edf_transform_prefix
  apply prefix_map_property_invariance
    (fun s => completed_jobs_dont_execute (Job := Job) s ∧
              jobs_must_arrive_to_execute (Job := Job) s ∧
              all_deadlines_met (Job := Job) s)
  · intro s t ⟨COMP, ARR, DL⟩
    exact ⟨mea_completed_jobs s ARR COMP DL t,
           mea_jobs_must_arrive s ARR COMP DL t,
           mea_no_deadline_misses s ARR COMP DL t⟩
  · exact ⟨H_completed_dont_execute, H_jobs_must_arrive, H_no_deadline_misses⟩

include H_jobs_must_arrive H_completed_dont_execute H_no_deadline_misses in
theorem edf_prefix_jobs_must_arrive :
    jobs_must_arrive_to_execute (Job := Job) (edf_transform_prefix sched horizon) :=
  (edf_prefix_well_formedness sched H_jobs_must_arrive H_completed_dont_execute H_no_deadline_misses horizon).2.1

include H_jobs_must_arrive H_completed_dont_execute H_no_deadline_misses in
theorem edf_prefix_scheduled_job_has_later_deadline (j : Job) (t : instant)
    (h : scheduled_at (edf_transform_prefix sched horizon) j t = true) :
    t < job_deadline j := by
  have ⟨COMP, _, DL⟩ := edf_prefix_well_formedness sched H_jobs_must_arrive H_completed_dont_execute H_no_deadline_misses horizon
  exact scheduled_at_implies_later_deadline _ COMP ideal_proc_model_ensures_ideal_progress j t (DL j t h) h

include H_jobs_must_arrive H_completed_dont_execute H_no_deadline_misses in
theorem edf_prefix_job_scheduled (j : Job) :
    ∀ t, scheduled_at (edf_transform_prefix sched horizon) j t = true →
    ∃ t', scheduled_at sched j t' = true := by
  unfold edf_transform_prefix
  apply prefix_map_property_invariance
    (fun s => ∀ t, scheduled_at s j t = true → ∃ t', scheduled_at sched j t' = true)
  · intro s t_ref h_prop t_val h_sched
    obtain ⟨t'', h''⟩ := mea_job_scheduled s t_ref j t_val h_sched
    exact h_prop t'' h''
  · exact fun t h => ⟨t, h⟩

include H_jobs_must_arrive H_completed_dont_execute H_no_deadline_misses in
theorem edf_prefix_job_scheduled' (j : Job) (t : instant)
    (h : scheduled_at sched j t = true) :
    ∃ t', scheduled_at (edf_transform_prefix sched horizon) j t' = true := by
  unfold edf_transform_prefix
  apply prefix_map_property_invariance
    (fun s => ∃ t', scheduled_at s j t' = true)
  · intro s t_ref ⟨t', h'⟩
    exact mea_job_scheduled' s t_ref j t' h'
  · exact ⟨t, h⟩

include H_jobs_must_arrive H_completed_dont_execute H_no_deadline_misses in
theorem edf_prefix_guarantee :
    ∀ t, t < horizon → EDF_at Job (processor_state Job) (edf_transform_prefix sched horizon) t := by
  unfold edf_transform_prefix
  apply prefix_map_pointwise_property
    (fun s => completed_jobs_dont_execute (Job := Job) s ∧
              jobs_must_arrive_to_execute (Job := Job) s ∧
              all_deadlines_met (Job := Job) s)
    (EDF_at Job (processor_state Job))
    (make_edf_at (Job := Job))
  · intro s t_ref ⟨COMP, ARR, DL⟩
    exact ⟨mea_completed_jobs s ARR COMP DL t_ref,
           mea_jobs_must_arrive s ARR COMP DL t_ref,
           mea_no_deadline_misses s ARR COMP DL t_ref⟩
  · intro s t_ref ⟨COMP, ARR, DL⟩ h_edf_prefix
    exact mea_EDF_widen s ARR COMP DL t_ref h_edf_prefix
  · exact ⟨H_completed_dont_execute, H_jobs_must_arrive, H_no_deadline_misses⟩

section EdfPrefixArrivalSequence
variable (arr_seq : arrival_sequence Job)
variable (H_from_arr_seq : jobs_come_from_arrival_sequence sched arr_seq)

include H_from_arr_seq in
theorem edf_prefix_jobs_come_from_arrival_sequence :
    jobs_come_from_arrival_sequence (edf_transform_prefix sched horizon) arr_seq := by
  unfold edf_transform_prefix
  apply prefix_map_property_invariance
    (fun s => jobs_come_from_arrival_sequence s arr_seq)
  · intro s t_ref h; exact mea_jobs_come_from_arrival_sequence s t_ref arr_seq h
  · exact H_from_arr_seq
end EdfPrefixArrivalSequence

end EDFPrefixFacts

/-! ## EDFPrefixInclusion -/

section EDFPrefixInclusion

variable {Job : JobType} [JobCost Job] [JobDeadline Job] [JobArrival Job]
variable [DecidableEq Job]
variable (sched : schedule (processor_state Job))
variable (H_jobs_must_arrive : jobs_must_arrive_to_execute (Job := Job) sched)
variable (H_completed_dont_execute : completed_jobs_dont_execute (Job := Job) sched)
variable (H_no_deadline_misses : all_deadlines_met (Job := Job) sched)

include H_jobs_must_arrive H_completed_dont_execute H_no_deadline_misses in
theorem edf_prefix_inclusion (h1 h2 : instant) :
    h1 ≤ h2 → ∀ t, t < h1 →
    (edf_transform_prefix sched h1) t = (edf_transform_prefix sched h2) t := by
  intro h_le
  induction h2 with
  | zero => intro t ht; exact absurd (Nat.lt_of_lt_of_le ht h_le) (Nat.not_lt_zero _)
  | succ n ih =>
    intro t ht
    rcases Nat.eq_or_lt_of_le h_le with rfl | hlt
    · rfl
    · have h_le_n : h1 ≤ n := Nat.lt_succ_iff.mp hlt
      have ht_n : t < n := Nat.lt_of_lt_of_le ht h_le_n
      rw [ih h_le_n t ht]
      set sched_n := edf_transform_prefix sched n
      change sched_n t = (make_edf_at sched_n n) t
      cases hsn : sched_n n with
      | none => rw [make_edf_at_none _ _ hsn]
      | some j =>
        rw [make_edf_at_some sched_n n j hsn]
        have ⟨C, A, D⟩ := edf_prefix_well_formedness sched H_jobs_must_arrive H_completed_dont_execute H_no_deadline_misses n
        have h_sj : scheduled_at sched_n j n = true := by
          rw [scheduled_at_def]; exact decide_eq_true hsn
        have h_dl : n < job_deadline j :=
          scheduled_at_implies_later_deadline sched_n C ideal_proc_model_ensures_ideal_progress j n (D j n h_sj) h_sj
        have h_fsc_ge := fsc_range1 sched_n A j n h_sj h_dl
        exact swap_before_invariant sched_n n _ h_fsc_ge t ht_n

end EDFPrefixInclusion

section EDFTransformFacts

variable {Job : JobType} [JobCost Job] [JobDeadline Job] [JobArrival Job]
variable [DecidableEq Job]

variable (sched : schedule (processor_state Job))
variable (H_jobs_must_arrive : jobs_must_arrive_to_execute (Job := Job) sched)
variable (H_completed_dont_execute : completed_jobs_dont_execute (Job := Job) sched)
variable (H_all_deadlines_met : all_deadlines_met (Job := Job) sched)

-- Helper: the schedule value at time i under edf_transform agrees with any
-- prefix of horizon > i, via edf_prefix_inclusion.
include H_jobs_must_arrive H_completed_dont_execute H_all_deadlines_met in
private theorem edf_transform_at_prefix (i N : instant) (h : i < N) :
    (edf_transform sched) i = (edf_transform_prefix sched N) i := by
  show edf_transform_prefix sched (i + 1) i = edf_transform_prefix sched N i
  have h1 : i + 1 ≤ N := Nat.succ_le_of_lt h
  have h2 : i < i + 1 := Nat.lt_succ_iff.mpr (Nat.le_refl i)
  exact edf_prefix_inclusion sched H_jobs_must_arrive H_completed_dont_execute H_all_deadlines_met
    (i + 1) N h1 i h2

-- Helper: service under edf_transform equals service under any prefix of horizon ≥ t.
include H_jobs_must_arrive H_completed_dont_execute H_all_deadlines_met in
private theorem edf_transform_service_eq (j : Job) (t N : instant) (h : t ≤ N) :
    service (edf_transform sched) j t = service (edf_transform_prefix sched N) j t := by
  unfold service service_during
  apply Finset.sum_congr rfl
  intro i hi; simp only [Finset.mem_Ico] at hi
  unfold service_at; congr 1
  exact edf_transform_at_prefix sched H_jobs_must_arrive H_completed_dont_execute H_all_deadlines_met
    i N (Nat.lt_of_lt_of_le hi.2 h)

include H_jobs_must_arrive H_completed_dont_execute H_all_deadlines_met in
theorem edf_transform_ensures_edf :
    EDF_schedule Job (processor_state Job) (edf_transform sched) := by
  intro t j sched_j t' j' h_le sched_j' arr_j'
  have h_incl := edf_prefix_inclusion sched H_jobs_must_arrive H_completed_dont_execute H_all_deadlines_met
    (t + 1) (t' + 1) (Nat.succ_le_succ h_le) t (Nat.lt_succ_iff.mpr (Nat.le_refl t))
  have sched_j2 : scheduled_at (edf_transform_prefix sched (t' + 1)) j t = true := by
    simp only [scheduled_at_def] at sched_j ⊢; rw [← h_incl]; exact sched_j
  exact edf_prefix_guarantee sched H_jobs_must_arrive H_completed_dont_execute H_all_deadlines_met
    (t' + 1) t (Nat.lt_succ_of_le h_le) j sched_j2 t' j' h_le sched_j' arr_j'

include H_jobs_must_arrive H_completed_dont_execute H_all_deadlines_met in
theorem edf_transform_jobs_must_arrive :
    jobs_must_arrive_to_execute (Job := Job) (edf_transform sched) := by
  intro j t sched_j
  exact edf_prefix_jobs_must_arrive sched H_jobs_must_arrive H_completed_dont_execute H_all_deadlines_met
    (t + 1) j t sched_j

include H_jobs_must_arrive H_completed_dont_execute H_all_deadlines_met in
theorem edf_transform_completed_jobs_dont_execute :
    completed_jobs_dont_execute (Job := Job) (edf_transform sched) := by
  intro j t sched_j
  have ⟨COMP, _, _⟩ := edf_prefix_well_formedness sched H_jobs_must_arrive H_completed_dont_execute
    H_all_deadlines_met (t + 1)
  rw [edf_transform_service_eq sched H_jobs_must_arrive H_completed_dont_execute H_all_deadlines_met
    j t (t + 1) (Nat.le_succ t)]
  exact COMP j t sched_j

include H_jobs_must_arrive H_completed_dont_execute H_all_deadlines_met in
theorem edf_transform_deadlines_met :
    all_deadlines_met (Job := Job) (edf_transform sched) := by
  intro j t sched_j
  have h_dl := edf_prefix_scheduled_job_has_later_deadline sched H_jobs_must_arrive
    H_completed_dont_execute H_all_deadlines_met (t + 1) j t sched_j
  have ⟨_, _, DL⟩ := edf_prefix_well_formedness sched H_jobs_must_arrive H_completed_dont_execute
    H_all_deadlines_met (job_deadline j)
  have sched_j_dl : scheduled_at (edf_transform_prefix sched (job_deadline j)) j t = true := by
    simp only [scheduled_at_def] at sched_j ⊢
    have h_incl := edf_prefix_inclusion sched H_jobs_must_arrive H_completed_dont_execute H_all_deadlines_met
      (t + 1) (job_deadline j) (Nat.succ_le_of_lt h_dl) t (Nat.lt_succ_iff.mpr (Nat.le_refl t))
    rw [← h_incl]; exact sched_j
  have DL_j := DL j t sched_j_dl
  unfold job_meets_deadline completed_by at DL_j ⊢
  rw [edf_transform_service_eq sched H_jobs_must_arrive H_completed_dont_execute H_all_deadlines_met
    j (job_deadline j) (job_deadline j) (Nat.le_refl _)]
  exact DL_j

include H_jobs_must_arrive H_completed_dont_execute H_all_deadlines_met in
theorem edf_transform_job_scheduled (j : Job) (t : instant) :
    scheduled_at (edf_transform sched) j t = true →
    ∃ t', scheduled_at sched j t' = true := by
  intro sched_j
  exact edf_prefix_job_scheduled sched H_jobs_must_arrive H_completed_dont_execute H_all_deadlines_met
    (t + 1) j t sched_j

include H_jobs_must_arrive H_completed_dont_execute H_all_deadlines_met in
theorem edf_transform_job_scheduled' (j : Job) (t : instant) :
    scheduled_at sched j t = true →
    ∃ t', scheduled_at (edf_transform sched) j t' = true := by
  intro sched_j
  obtain ⟨t', sched_t'⟩ := edf_prefix_job_scheduled' sched H_jobs_must_arrive H_completed_dont_execute
    H_all_deadlines_met (job_deadline j) j t sched_j
  have h_lt := edf_prefix_scheduled_job_has_later_deadline sched H_jobs_must_arrive
    H_completed_dont_execute H_all_deadlines_met (job_deadline j) j t' sched_t'
  refine ⟨t', ?_⟩
  simp only [scheduled_at_def] at sched_t' ⊢
  change decide (edf_transform_prefix sched (t' + 1) t' = some j) = true
  have h_incl := edf_prefix_inclusion sched H_jobs_must_arrive H_completed_dont_execute H_all_deadlines_met
    (t' + 1) (job_deadline j) (Nat.succ_le_of_lt h_lt) t' (Nat.lt_succ_iff.mpr (Nat.le_refl t'))
  rw [h_incl]; exact sched_t'

end EDFTransformFacts

section OptimalityFacts

variable {Job : JobType} [JobCost Job] [JobDeadline Job] [JobArrival Job]
variable [DecidableEq Job]

variable (arr_seq : arrival_sequence Job)
variable (H_arr_seq_valid : valid_arrival_sequence arr_seq)

include H_arr_seq_valid in
theorem edf_schedule_is_valid
    (any_sched : schedule (processor_state Job))
    (VALID : valid_schedule any_sched arr_seq)
    (DL_MET : all_deadlines_met (Job := Job) any_sched) :
    valid_schedule (edf_transform any_sched) arr_seq := by
  obtain ⟨COME, READY⟩ := VALID
  have ARR := jobs_must_arrive_to_be_ready any_sched READY
  have COMP := completed_jobs_are_not_ready any_sched READY
  constructor
  · intro j t sched_j
    exact edf_prefix_jobs_come_from_arrival_sequence any_sched (t + 1) arr_seq COME j t sched_j
  · exact basic_readiness_compliance (edf_transform any_sched)
      (edf_transform_jobs_must_arrive any_sched ARR COMP DL_MET)
      (edf_transform_completed_jobs_dont_execute any_sched ARR COMP DL_MET)

include H_arr_seq_valid in
theorem edf_schedule_meets_all_deadlines_wrt_arrivals
    (any_sched : schedule (processor_state Job))
    (VALID : valid_schedule any_sched arr_seq)
    (DL_ARR_MET : all_deadlines_of_arrivals_met arr_seq any_sched) :
    all_deadlines_of_arrivals_met arr_seq (edf_transform any_sched) := by
  obtain ⟨COME, READY⟩ := VALID
  have ARR := jobs_must_arrive_to_be_ready any_sched READY
  have COMP := completed_jobs_are_not_ready any_sched READY
  have DL_MET := all_deadlines_met_in_valid_schedule arr_seq any_sched COME DL_ARR_MET
  intro j h_arrives
  by_cases h_cost : job_cost j = 0
  · unfold job_meets_deadline completed_by; simp [h_cost]
  · have h_pos : 0 < job_cost j := Nat.pos_of_ne_zero h_cost
    have COMP_j := DL_ARR_MET j h_arrives
    unfold job_meets_deadline completed_by at COMP_j
    obtain ⟨t', _, _, sched_t'⟩ := completed_implies_scheduled_before any_sched j h_pos ARR
      (job_deadline j) COMP_j
    obtain ⟨t'', sched_t''⟩ := edf_transform_job_scheduled' any_sched ARR COMP DL_MET j t' sched_t'
    exact edf_transform_deadlines_met any_sched ARR COMP DL_MET j t'' sched_t''

end OptimalityFacts
