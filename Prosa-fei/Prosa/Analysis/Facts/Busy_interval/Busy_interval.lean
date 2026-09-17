-- Translated from: ../rt-proofs/analysis/facts/busy_interval/busy_interval.v
import Prosa.Model.Schedule.Work_conserving
import Prosa.Analysis.Definitions.Job_properties
import Prosa.Analysis.Definitions.Priority_inversion
import Prosa.Analysis.Facts.Behavior.All
import Prosa.Analysis.Facts.Model.Service_of_jobs
import Prosa.Model.Processor.Ideal
import Prosa.Model.Readiness.Basic

namespace Prosa.Analysis.Facts.Busy_interval.Busy_interval

open Prosa.Behavior.Job
open Prosa.Behavior.Time
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Ready
open Prosa.Model.Task.Concept
open Prosa.Model.Priority.Classes
open Prosa.Model.Processor.Ideal
open Prosa.Model.Schedule.Work_conserving
open Prosa.Analysis.Definitions.Job_properties
open Prosa.Analysis.Definitions.Priority_inversion
open Prosa.Analysis.Definitions.Busy_interval
open Prosa.Analysis.Facts.Behavior.Completion
open Prosa.Analysis.Facts.Behavior.Service
open Prosa.Analysis.Facts.Model.Service_of_jobs
open Prosa.Model.Aggregate.Service_of_jobs
open Prosa.Model.Aggregate.Workload
open Prosa.Analysis.Facts.Model.Ideal_schedule
open Prosa.Analysis.Facts.Behavior.Arrivals
open Prosa.Model.Readiness.Basic

set_option linter.dupNamespace false

section ExistsBusyIntervalJLFP

variable {Task : TaskType}
variable [TaskCost Task]
variable [DecidableEq Task]

variable {Job : JobType}
variable [DecidableEq Job]
variable [JobTask Job Task]
variable [JobArrival Job]
variable [JobCost Job]

variable (arr_seq : arrival_sequence Job)
variable (H_arrival_times_are_consistent : consistent_arrival_times arr_seq)

variable (sched : schedule (processor_state Job))
variable (H_jobs_come_from_arrival_sequence :
  jobs_come_from_arrival_sequence sched arr_seq)

variable (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute (Job := Job) sched)
variable (H_completed_jobs_dont_execute : completed_jobs_dont_execute (Job := Job) sched)

variable [JLFP_policy Job]

attribute [local instance] JLFP_to_JLDP

variable (tsk : Task)

variable (j : Job)
variable (H_from_arrival_sequence : arrives_in arr_seq j)
variable (H_job_task : job_of_task tsk j = true)
variable (H_job_cost_positive : job_cost_positive j)

section BasicLemma

variable (H_priority_is_reflexive : reflexive_priorities (Job := Job))

variable (t1 t2 : instant)
variable (H_busy_interval : busy_interval arr_seq sched j t1 t2)

include H_arrival_times_are_consistent H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_from_arrival_sequence H_job_task H_job_cost_positive H_priority_is_reflexive H_busy_interval in
theorem job_completes_within_busy_interval :
    completed_by sched j t2 := by
  obtain ⟨⟨_, _, _, hle_arr, harr_lt⟩, hquiet⟩ := H_busy_interval
  exact hquiet j H_from_arrival_sequence (H_priority_is_reflexive 0 j) harr_lt

end BasicLemma

section ExistsPendingJob

variable (t1 t2 : instant)
variable (H_interval : t1 ≤ t2)
variable (H_quiet : quiet_time arr_seq sched j t1)
variable (H_not_quiet : ¬ quiet_time arr_seq sched j t2)

include H_arrival_times_are_consistent H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_from_arrival_sequence H_job_task H_job_cost_positive H_interval H_quiet H_not_quiet in
theorem not_quiet_implies_exists_pending_job :
    ∃ j_hp,
      arrives_in arr_seq j_hp ∧
      arrived_between j_hp t1 t2 ∧
      hep_job j_hp j = true ∧
      ¬ completed_by sched j_hp t2 := by
  by_contra HALL
  push_neg at HALL
  apply H_not_quiet
  intro j_hp hIN hHP hARRB
  by_cases hlt : job_arrival j_hp < t1
  · exact completion_monotonic sched j_hp t1 t2 H_interval (H_quiet j_hp hIN hHP hlt)
  · push_neg at hlt
    exact HALL j_hp hIN ⟨hlt, hARRB⟩ hHP

end ExistsPendingJob

section ProcessorAlwaysBusy

variable (H_work_conserving : work_conserving arr_seq sched)

variable (H_priority_is_reflexive : reflexive_priorities (Job := Job))
variable (H_priority_is_transitive : transitive_priorities (Job := Job))

variable (t1 t2 : instant)
variable (H_busy_interval_prefix : busy_interval_prefix arr_seq sched j t1 t2)

include H_arrival_times_are_consistent H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_from_arrival_sequence H_job_task H_job_cost_positive H_work_conserving H_priority_is_reflexive H_priority_is_transitive H_busy_interval_prefix in
theorem idle_time_implies_quiet_time_at_the_next_time_instant :
    ∀ (t : instant),
      is_idle sched t →
      quiet_time arr_seq sched j (t + 1) := by
  intro t hIDLE jhp hARR hHP hAB
  have hle : job_arrival jhp ≤ t := Nat.lt_succ_iff.mp hAB
  by_contra hNCOMP
  have hNCOMP_t : ¬ completed_by sched jhp t := fun hc =>
    hNCOMP (completion_monotonic sched jhp t (t + 1) (Nat.le_succ t) hc)
  have hIDLE' : sched t = none := hIDLE
  have hNSCHED : scheduled_at sched jhp t = false := by
    rw [scheduled_at_def, hIDLE']
    rfl
  have hBL : backlogged sched jhp t = true := by
    simp only [backlogged, Bool.and_eq_true, Bool.not_eq_true_eq_eq_false]
    constructor
    · show job_ready sched jhp t = true
      change (decide (job_arrival jhp ≤ t) && !decide (service sched jhp t ≥ job_cost jhp)) = true
      simp only [decide_eq_true_eq, Bool.and_eq_true, Bool.not_eq_true_eq_eq_false,
        decide_eq_false_iff_not]
      exact ⟨hle, hNCOMP_t⟩
    · exact hNSCHED
  have ⟨jo, hSCHED⟩ := H_work_conserving jhp t hARR hBL
  rw [scheduled_at_def, hIDLE'] at hSCHED
  simp at hSCHED

include H_arrival_times_are_consistent H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_from_arrival_sequence H_job_task H_job_cost_positive H_work_conserving H_priority_is_reflexive H_priority_is_transitive H_busy_interval_prefix in
theorem pending_hp_job_exists :
    ∀ t,
      t1 ≤ t ∧ t < t2 →
      ∃ jhp,
        arrives_in arr_seq jhp ∧
        pending sched jhp t ∧
        hep_job jhp j = true := by
  intro t ⟨hGE, hLT⟩
  obtain ⟨_, hQTt1, hNQT, hREL_le, hREL_lt⟩ := H_busy_interval_prefix
  by_contra hNEX
  push_neg at hNEX
  -- hNEX : ∀ jhp, arrives_in arr_seq jhp → pending sched jhp t → hep_job jhp j ≠ true
  -- From hNEX: any hep job that has arrived by t is completed at t
  have hCOMP_at_t : ∀ jhp, arrives_in arr_seq jhp → hep_job jhp j = true →
      has_arrived jhp t → completed_by sched jhp t := by
    intro jhp hARR hHP hHA
    by_contra hNC
    exact hNEX jhp hARR ⟨hHA, hNC⟩ hHP
  -- Case: t1 = t or t1 < t
  rcases Nat.eq_or_lt_of_le hGE with heq_t | hGT
  · -- t1 = t. Need to show contradiction.
    -- Subcase: t1 + 1 < t2 or t1 + 1 ≥ t2
    rcases Nat.lt_or_ge (t1 + 1) t2 with hlt2 | hge2
    · -- t1 + 1 < t2: show quiet_time (t1+1), contradicting NQT
      have hQ : quiet_time arr_seq sched j (t1 + 1) := by
        intro jhp hARR hHP hAB
        have hle' : job_arrival jhp ≤ t := by
          have := Nat.lt_succ_iff.mp (heq_t ▸ hAB : job_arrival jhp < t + 1)
          exact this
        exact completion_monotonic sched jhp t (t1 + 1) (heq_t ▸ Nat.le_succ t)
          (hCOMP_at_t jhp hARR hHP hle')
      exact absurd hQ (hNQT (t1 + 1) ⟨Nat.lt_succ_of_le (Nat.le_refl t1), hlt2⟩)
    · -- t1 + 1 ≥ t2: since t < t2 and t1 = t, we get t1 + 1 = t2
      -- job j is pending at t = t1, since job_arrival j ∈ [t1, t2) and t2 = t1 + 1
      have heq_arr : job_arrival j = t := by
        have h1 : t ≤ job_arrival j := heq_t ▸ hREL_le
        have h2 : job_arrival j < t + 1 := Nat.lt_of_lt_of_le hREL_lt (heq_t ▸ hge2)
        exact Nat.le_antisymm (Nat.lt_succ_iff.mp h2) h1
      have hPEND_j : pending sched j t := by
        rw [← heq_arr]
        exact job_pending_at_arrival sched j H_job_cost_positive H_jobs_must_arrive_to_execute
      exact hNEX j H_from_arrival_sequence hPEND_j (H_priority_is_reflexive 0 j)
  · -- t1 < t: show quiet_time at t, contradicting NQT
    have hQ : quiet_time arr_seq sched j t := by
      intro jhp hARR hHP hAB
      exact hCOMP_at_t jhp hARR hHP (Nat.le_of_lt hAB)
    exact absurd hQ (hNQT t ⟨hGT, hLT⟩)

include H_arrival_times_are_consistent H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_from_arrival_sequence H_job_task H_job_cost_positive H_work_conserving H_priority_is_reflexive H_priority_is_transitive H_busy_interval_prefix in
theorem not_quiet_implies_not_idle :
    ∀ t,
      t1 ≤ t ∧ t < t2 →
      ¬ is_idle sched t := by
  intro t hNEQ hIDLE
  have hphe := @pending_hp_job_exists _ _ _ _ _ _ _ _ arr_seq H_arrival_times_are_consistent sched
    H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute _ _ j
    H_from_arrival_sequence H_job_task H_job_cost_positive H_work_conserving H_priority_is_reflexive
    H_priority_is_transitive t1 t2 H_busy_interval_prefix
  obtain ⟨jhp, hARR, hPEND, hHP⟩ := hphe t hNEQ
  have hIDLE' : sched t = none := hIDLE
  have hNSCHED : scheduled_at sched jhp t = false := by
    rw [scheduled_at_def, hIDLE']; rfl
  have hBL : backlogged sched jhp t = true := by
    simp only [backlogged, Bool.and_eq_true, Bool.not_eq_true_eq_eq_false]
    constructor
    · show job_ready sched jhp t = true
      change (decide (job_arrival jhp ≤ t) && !decide (service sched jhp t ≥ job_cost jhp)) = true
      simp only [decide_eq_true_eq, Bool.and_eq_true, Bool.not_eq_true_eq_eq_false,
        decide_eq_false_iff_not]
      exact hPEND
    · exact hNSCHED
  obtain ⟨jo, hSCHED⟩ := H_work_conserving jhp t hARR hBL
  rw [scheduled_at_def, hIDLE'] at hSCHED
  simp at hSCHED

end ProcessorAlwaysBusy

section QuietTimeAndServiceOfJobs

variable (H_work_conserving : work_conserving arr_seq sched)

variable (H_arrival_sequence_is_a_set : arrival_sequence_uniq arr_seq)

variable (t1 : instant)
variable (H_quiet_time : quiet_time arr_seq sched j t1)

variable (Δ : duration)
variable (H_no_quiet_time : ∀ t, t1 < t ∧ t ≤ t1 + Δ → ¬ quiet_time arr_seq sched j t)

include H_arrival_times_are_consistent H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_from_arrival_sequence H_job_task H_job_cost_positive H_work_conserving H_arrival_sequence_is_a_set H_quiet_time H_no_quiet_time in
theorem hep_jobs_receive_no_service_before_quiet_time :
    service_of_higher_or_equal_priority_jobs
      sched (arrivals_between arr_seq t1 (t1 + Δ)) j t1 (t1 + Δ) =
    service_of_higher_or_equal_priority_jobs
      sched (arrivals_between arr_seq 0 (t1 + Δ)) j t1 (t1 + Δ) := by
  unfold service_of_higher_or_equal_priority_jobs service_of_jobs
  rw [arrivals_between_cat arr_seq 0 t1 (t1 + Δ) (Nat.zero_le _) (Nat.le_add_right _ _)]
  rw [List.filter_append, List.map_append, List.sum_append]
  suffices h_zero :
    ((arrivals_between arr_seq 0 t1).filter (fun j_hp => hep_job j_hp j) |>.map
      (fun j_hp => service_during sched j_hp t1 (t1 + Δ))).sum = 0 by
    simp only [work] at *; omega
  apply List.sum_eq_zero
  intro x hx
  rw [List.mem_map] at hx
  obtain ⟨jhp, hjhp_mem, rfl⟩ := hx
  rw [List.mem_filter] at hjhp_mem
  obtain ⟨hIN, hHP⟩ := hjhp_mem
  -- jhp arrived before t1 and is hep, so completed at t1 by quiet time
  have hARR := in_arrivals_implies_arrived arr_seq H_arrival_times_are_consistent jhp 0 t1 hIN
  have hAB := in_arrivals_implies_arrived_before arr_seq H_arrival_times_are_consistent jhp t1 hIN
  have hCOMP := H_quiet_time jhp hARR hHP hAB
  -- completed at t1, so not scheduled during [t1, t1+Δ)
  apply Finset.sum_eq_zero
  intro t ht
  rw [Finset.mem_Ico] at ht
  have hCOMPt := completion_monotonic sched jhp t1 t (by simp only [instant] at *; omega) hCOMP
  have hNSCHED := completed_implies_not_scheduled sched jhp H_completed_jobs_dont_execute t hCOMPt
  exact not_scheduled_implies_no_service sched jhp t hNSCHED

include H_arrival_times_are_consistent H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_from_arrival_sequence H_job_task H_job_cost_positive H_work_conserving H_arrival_sequence_is_a_set H_quiet_time H_no_quiet_time in
theorem no_idle_time_within_non_quiet_time_interval :
    service_of_jobs sched (fun _ => true) (arrivals_between arr_seq 0 (t1 + Δ)) t1 (t1 + Δ) = Δ := by
  apply Nat.le_antisymm
  · -- Upper bound: service ≤ Δ
    have := service_of_jobs_le_length_of_interval' arr_seq H_arrival_times_are_consistent sched
      H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
      (fun _ => true) (arrivals_between arr_seq 0 (t1 + Δ))
      (arrivals_uniq arr_seq H_arrival_times_are_consistent H_arrival_sequence_is_a_set 0 (t1 + Δ))
      t1 (t1 + Δ)
    simp only [instant, work] at *; omega
  · -- Lower bound: Δ ≤ service
    -- Proceed by contrapositive: assume service < Δ, derive idle time, get contradiction
    by_contra h
    push_neg at h
    -- h : service_of_jobs ... < Δ
    have h' : service_of_jobs sched (fun _ => true) (arrivals_between arr_seq 0 (t1 + Δ)) t1 (t1 + Δ) < t1 + Δ - t1 := by
      simp only [instant, work] at *; omega
    obtain ⟨t, ht1, ht2, hIDLE⟩ := low_service_implies_existence_of_idle_time arr_seq
      H_arrival_times_are_consistent sched H_jobs_come_from_arrival_sequence
      H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute t1 (t1 + Δ) h'
    -- Show that being idle at t leads to quiet time at t+1, contradicting H_no_quiet_time
    -- First show quiet time at t+1
    have hQUIET : quiet_time arr_seq sched j (t + 1) := by
      intro jhp hARR hHP hAB
      -- jhp arrived before t+1, so arrived at or before t
      have hle : job_arrival jhp ≤ t := Nat.lt_succ_iff.mp hAB
      by_contra hNCOMP
      -- jhp is not completed at t+1, hence not completed at t
      have hNCOMP_t : ¬ completed_by sched jhp t := fun hc =>
        hNCOMP (completion_monotonic sched jhp t (t + 1) (Nat.le_succ t) hc)
      have hIDLE' : sched t = none := hIDLE
      have hNSCHED : scheduled_at sched jhp t = false := by
        rw [scheduled_at_def, hIDLE']; rfl
      have hBL : backlogged sched jhp t = true := by
        simp only [backlogged, Bool.and_eq_true, Bool.not_eq_true_eq_eq_false]
        constructor
        · show job_ready sched jhp t = true
          change (decide (job_arrival jhp ≤ t) && !decide (service sched jhp t ≥ job_cost jhp)) = true
          simp only [decide_eq_true_eq, Bool.and_eq_true, Bool.not_eq_true_eq_eq_false,
            decide_eq_false_iff_not]
          exact ⟨hle, hNCOMP_t⟩
        · exact hNSCHED
      obtain ⟨jo, hSCHED⟩ := H_work_conserving jhp t hARR hBL
      rw [scheduled_at_def, hIDLE'] at hSCHED
      simp at hSCHED
    -- Now: t1 ≤ t < t1 + Δ. Either t = t1 or t > t1.
    rcases Nat.eq_or_lt_of_le ht1 with rfl | hGT
    · -- t = t1: quiet at t1+1, need t1 < t1+1 ≤ t1 + Δ
      by_cases hΔ0 : Δ = 0
      · subst hΔ0; simp only [instant, work] at h; omega
      · have hΔpos : Δ > 0 := Nat.pos_of_ne_zero hΔ0
        exact H_no_quiet_time (t1 + 1) ⟨Nat.lt_succ_of_le le_rfl, by simp only [instant] at *; omega⟩ hQUIET
    · -- t > t1: quiet at t+1, need t1 < t+1 ≤ t1 + Δ
      exact H_no_quiet_time (t + 1) ⟨by simp only [instant] at *; omega, by simp only [instant] at *; omega⟩ hQUIET

end QuietTimeAndServiceOfJobs

section BoundingBusyInterval

variable (H_work_conserving : work_conserving arr_seq sched)

variable (H_arrival_sequence_is_a_set : arrival_sequence_uniq arr_seq)

variable (H_priority_is_reflexive : reflexive_priorities (Job := Job))
variable (H_priority_is_transitive : transitive_priorities (Job := Job))

section BoundingBusyInterval'

variable (t_busy : instant)
variable (H_j_is_pending : pending sched j t_busy)

section LowerBound

include H_arrival_times_are_consistent H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_from_arrival_sequence H_job_cost_positive H_work_conserving H_arrival_sequence_is_a_set H_priority_is_reflexive H_j_is_pending in
theorem exists_busy_interval_prefix :
    ∃ t1,
      busy_interval_prefix arr_seq sched j t1 (t_busy + 1) ∧
      t1 ≤ job_arrival j ∧ job_arrival j ≤ t_busy := by
  -- Decide whether there exists a quiet time t in [0, t_busy+1)
  by_cases hEX : ∃ t, t ≤ t_busy ∧ quiet_time arr_seq sched j t
  · -- Case 1: there exists a quiet time ≤ t_busy
    -- Take last0 = the maximal such t (using Nat.find on the reversed property)
    -- We use the fact that the set of quiet times ≤ t_busy is finite and nonempty
    have hEX' : ∃ t, t ≤ t_busy ∧ quiet_time arr_seq sched j t := hEX
    -- Define last0 as the maximum t ≤ t_busy with quiet_time
    -- Use Nat well-ordering to find the max
    -- Equivalently, find the minimum "gap": min k such that ¬ quiet_time (t_busy - k) with k < t_busy+1
    -- Actually, let's use a cleaner approach: define the set and take Sup
    -- Simpler: use Nat.findGreatest
    have hDP : DecidablePred (fun t => quiet_time_dec arr_seq sched j t = true) :=
      fun t => inferInstanceAs (Decidable (quiet_time_dec arr_seq sched j t = true))
    set last0 := @Nat.findGreatest (fun t => quiet_time_dec arr_seq sched j t = true) hDP t_busy with hlast0_def
    have hPRED : quiet_time_dec arr_seq sched j last0 = true := by
      obtain ⟨t, htb, hq⟩ := hEX'
      exact @Nat.findGreatest_spec t (fun t => quiet_time_dec arr_seq sched j t = true) hDP t_busy
        htb ((quiet_time_P arr_seq H_arrival_times_are_consistent sched j t).mpr hq)
    have hQUIET : quiet_time arr_seq sched j last0 :=
      (quiet_time_P arr_seq H_arrival_times_are_consistent sched j last0).mp hPRED
    have hlast0_le : last0 ≤ t_busy := @Nat.findGreatest_le _ hDP t_busy
    -- Show last0 ≤ job_arrival j
    have hJA_ge : last0 ≤ job_arrival j := by
      by_contra hBEFORE
      push_neg at hBEFORE
      -- last0 > job_arrival j, so j arrived before last0
      -- j is hep to itself
      have hHP := H_priority_is_reflexive 0 j
      -- j arrived before last0
      have hAB : arrived_before j last0 := hBEFORE
      -- So j is completed at last0
      have hCOMP := hQUIET j H_from_arrival_sequence hHP hAB
      -- j is completed at last0, so completed at t_busy (monotonicity)
      have hCOMP_busy := completion_monotonic sched j last0 t_busy hlast0_le hCOMP
      -- But j is pending at t_busy, contradiction
      exact H_j_is_pending.2 hCOMP_busy
    -- Show job_arrival j ≤ t_busy
    have hJA_le : job_arrival j ≤ t_busy := H_j_is_pending.1
    -- Show last0 < t_busy + 1
    have hLT : last0 < t_busy + 1 := Nat.lt_succ_of_le hlast0_le
    -- Show no quiet time in (last0, t_busy+1)
    have hNQT : ∀ t0, last0 < t0 ∧ t0 < t_busy + 1 → ¬ quiet_time arr_seq sched j t0 := by
      intro t0 ⟨hGT, hLTbusy⟩ hQ
      have ht0_le : t0 ≤ t_busy := Nat.lt_succ_iff.mp hLTbusy
      have hDEC : quiet_time_dec arr_seq sched j t0 = true :=
        (quiet_time_P arr_seq H_arrival_times_are_consistent sched j t0).mpr hQ
      exact @Nat.findGreatest_is_greatest t0 (fun t => quiet_time_dec arr_seq sched j t = true) hDP t_busy hGT ht0_le hDEC
    refine ⟨last0, ⟨hLT, hQUIET, hNQT, hJA_ge, Nat.lt_succ_of_le hJA_le⟩, hJA_ge, hJA_le⟩
  · -- Case 2: no quiet time in [0, t_busy]
    push_neg at hEX
    -- hEX : ∀ t, t ≤ t_busy → ¬ quiet_time arr_seq sched j t
    -- t1 = 0 works
    refine ⟨0, ⟨Nat.succ_pos _, ?_, ?_, Nat.zero_le _, Nat.lt_succ_of_le H_j_is_pending.1⟩,
      Nat.zero_le _, H_j_is_pending.1⟩
    · -- quiet_time at 0: vacuously true (no job arrives before 0)
      intro jhp _ _ hAB
      exact absurd hAB (Nat.not_lt_zero _)
    · -- no quiet time in (0, t_busy + 1)
      intro t ⟨hGT, hLT⟩ hQ
      exact hEX t (Nat.lt_succ_iff.mp hLT) hQ

end LowerBound

section UpperBound

variable (t1 : instant)
variable (H_is_busy_prefix : busy_interval_prefix arr_seq sched j t1 (t_busy + 1))

variable (priority_inversion_bound : instant)
variable (H_priority_inversion_is_bounded :
  priority_inversion_of_job_is_bounded_by arr_seq sched j priority_inversion_bound)

variable (delta : duration)
variable (H_delta_positive : delta > 0)
variable (H_workload_is_bounded :
  priority_inversion_bound +
    workload_of_higher_or_equal_priority_jobs j (arrivals_between arr_seq t1 (t1 + delta)) ≤ delta)

section CannotBeBusyForSoLong

variable (H_no_quiet_time :
  ∀ t, t1 < t ∧ t ≤ t1 + delta → ¬ quiet_time arr_seq sched j t)

include H_arrival_times_are_consistent H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_from_arrival_sequence H_job_task H_job_cost_positive H_work_conserving H_arrival_sequence_is_a_set H_priority_is_reflexive H_priority_is_transitive H_j_is_pending H_is_busy_prefix H_priority_inversion_is_bounded H_delta_positive H_workload_is_bounded H_no_quiet_time in
theorem busy_interval_has_uninterrupted_service :
    delta ≤ priority_inversion_bound +
      service_of_higher_or_equal_priority_jobs
        sched (arrivals_between arr_seq t1 (t1 + delta)) j t1 (t1 + delta) := by
  have hPREFIX := H_is_busy_prefix
  obtain ⟨_, hQT, _, hEXj⟩ := H_is_busy_prefix
  -- Case split: delta ≤ priority_inversion_bound or not
  by_cases hKLE : delta ≤ priority_inversion_bound
  · -- Easy case: delta ≤ PIB ≤ PIB + hp_service
    exact Nat.le_trans hKLE (Nat.le_add_right _ _)
  · push_neg at hKLE
    -- Hard case: PIB < delta
    -- Key fact: total service of all jobs = delta (processor is never idle)
    have hTOTAL := no_idle_time_within_non_quiet_time_interval arr_seq
      H_arrival_times_are_consistent sched H_jobs_come_from_arrival_sequence
      H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute tsk j
      H_from_arrival_sequence H_job_task H_job_cost_positive H_work_conserving
      H_arrival_sequence_is_a_set t1 hQT delta H_no_quiet_time
    -- Key fact: hep service from [t1, t1+delta) arrivals = hep service from [0, t1+delta) arrivals
    have hHEP := hep_jobs_receive_no_service_before_quiet_time arr_seq
      H_arrival_times_are_consistent sched H_jobs_come_from_arrival_sequence
      H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute tsk j
      H_from_arrival_sequence H_job_task H_job_cost_positive H_work_conserving
      H_arrival_sequence_is_a_set t1 hQT delta H_no_quiet_time
    -- Now we need: delta ≤ PIB + hp_service_from_t1_arrivals
    -- We know: delta = total_service_of_all_jobs from [0, t1+delta)
    -- total_service = hep_service + non_hep_service
    -- non_hep_service ≤ cum_prio_inv ≤ PIB (via priority_inversion_is_bounded)
    -- So delta = hep_service + non_hep_service ≤ hep_service + PIB
    -- First, show cum_prio_inv ≤ PIB
    have hCPI_le : cumulative_priority_inversion sched j t1 (t1 + delta) ≤ priority_inversion_bound := by
      by_cases hLE : t1 + delta ≤ t_busy + 1
      · -- t1 + delta ≤ t_busy + 1: cum_prio_inv t1 (t1+delta) ≤ cum_prio_inv t1 (t_busy+1) ≤ PIB
        have hBND := H_priority_inversion_is_bounded t1 (t_busy + 1) hPREFIX
        calc cumulative_priority_inversion sched j t1 (t1 + delta)
            ≤ cumulative_priority_inversion sched j t1 (t_busy + 1) := by
              unfold cumulative_priority_inversion
              apply Finset.sum_le_sum_of_subset_of_nonneg
              · exact Finset.Ico_subset_Ico le_rfl hLE
              · intros; exact Nat.zero_le _
          _ ≤ priority_inversion_bound := hBND
      · push_neg at hLE
        -- t_busy + 1 < t1 + delta: need busy_interval_prefix for the larger interval
        -- The prefix [t1, t1 + delta) is a busy interval prefix because no quiet time in (t1, t1+delta]
        have hPREFIX' : busy_interval_prefix arr_seq sched j t1 (t1 + delta) := by
          have hd : (0 : ℕ) < delta := H_delta_positive
          refine ⟨Nat.lt_add_of_pos_right hd, hQT, ?_, ?_, ?_⟩
          · intro t ⟨hgt, hlt⟩
            exact H_no_quiet_time t ⟨hgt, Nat.le_of_lt hlt⟩
          · exact hPREFIX.2.2.2.1
          · have hlt := hPREFIX.2.2.2.2
            have hle := hLE
            simp only [instant] at *; omega
        exact H_priority_inversion_is_bounded t1 (t1 + delta) hPREFIX'
    -- Now we need to connect total_service, hep_service, and cum_prio_inv
    -- total_service = service_of_jobs sched (fun _ => true) (arrivals_between 0 (t1+delta)) t1 (t1+delta)
    -- = hep_service_from_0 + non_hep_service_from_0
    -- And hep_service_from_0 = hep_service_from_t1 (by hHEP)
    -- So delta = total_service ≤ cum_prio_inv + hep_service_from_0
    --                          = cum_prio_inv + hep_service_from_t1
    --                          ≤ PIB + hep_service_from_t1
    -- We need: delta ≤ cum_prio_inv + hep_service
    -- This requires: total_service ≤ cum_prio_inv + hep_service (from all [0, t1+delta))
    -- which follows from: non_hep_service ≤ cum_prio_inv
    -- Let's unfold and show the decomposition
    set all_jobs := arrivals_between arr_seq 0 (t1 + delta) with h_all_jobs
    set t1_jobs := arrivals_between arr_seq t1 (t1 + delta)
    -- service_of_jobs (predT) all_jobs = delta
    -- service_of_jobs (hep) all_jobs = hep_service_from_0 = hep_service_from_t1 (by hHEP)
    -- We want: delta ≤ cum_prio_inv + hep_service_from_t1 ≤ PIB + hep_service_from_t1
    -- It suffices to show: delta ≤ cum_prio_inv + hep_service_from_0
    -- i.e., total_service ≤ cum_prio_inv + hep_service_from_0
    -- i.e., total_service - hep_service_from_0 ≤ cum_prio_inv
    -- total_service - hep_service_from_0 is the service of non-hep jobs from all_jobs
    -- At each time t, either:
    --   - idle (contributes 0 to total and 0 to non-hep)
    --   - scheduled j1 with hep j1 j (contributes 1 to total, 0 to non-hep, 1 to hep)
    --   - scheduled j1 with ¬hep j1 j (contributes 1 to total, 1 to non-hep, 0 to hep; is prio inversion)
    -- So non-hep_service ≤ cum_prio_inv
    -- This is essentially what the Coq proof does with the exchange_big
    -- Let's try to show it more directly
    -- Step 1: show delta ≤ cum_prio_inv + service_of_hep from all arrivals [0, t1+delta)
    have hDECOMP : service_of_jobs sched (fun _ => true) all_jobs t1 (t1 + delta) ≤
        cumulative_priority_inversion sched j t1 (t1 + delta) +
        service_of_higher_or_equal_priority_jobs sched all_jobs j t1 (t1 + delta) := by
      -- At each time t in [t1, t1+delta):
      --   if idle: total=0, cum_prio_inv=0, hep_service=0 (ok)
      --   if scheduled j1 with hep: total=1, hep_service≥1 (ok)
      --   if scheduled j1 without hep: total=1, cum_prio_inv=1 (ok)
      unfold service_of_jobs service_of_higher_or_equal_priority_jobs service_of_jobs
        cumulative_priority_inversion is_priority_inversion
      simp only [service_during]
      -- Swap sums: ∑_j ∑_t → ∑_t ∑_j
      have h_swap_all : ∀ (l : List Job),
          (l.map (fun j => ∑ t' ∈ Finset.Ico t1 (t1 + delta), service_at sched j t')).sum =
          ∑ t' ∈ Finset.Ico t1 (t1 + delta), (l.map (fun j => service_at sched j t')).sum := by
        intro l; induction l with
        | nil => simp
        | cons a l ih => simp only [List.map_cons, List.sum_cons]; rw [ih, ← Finset.sum_add_distrib]
      rw [h_swap_all, h_swap_all]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro t ht
      rw [Finset.mem_Ico] at ht
      -- At each time t, show: predT_service ≤ prio_inv(t) + hep_service(t)
      cases hsched_t : sched t with
      | none =>
        -- Idle: all service_at = 0
        simp only [hsched_t]
        have : ((all_jobs.filter fun _ => true).map fun j => service_at sched j t).sum = 0 := by
          apply List.sum_eq_zero; intro x hx; rw [List.mem_map] at hx
          obtain ⟨j', _, rfl⟩ := hx
          apply not_scheduled_implies_no_service
          rw [scheduled_at_def, hsched_t]; rfl
        simp only [work, instant] at *; omega
      | some j1 =>
        -- Scheduled j1
        by_cases hHEP_j1 : hep_job j1 j = true
        · -- j1 is hep: prio_inv = 0, hep_service ≥ total_service
          have hPI : ((!hep_job j1 j).toNat) = 0 := by simp [hHEP_j1]
          have hARR_j1 : arrives_in arr_seq j1 := H_jobs_come_from_arrival_sequence j1 t (by rw [scheduled_at_def, hsched_t]; simp)
          have hHA_j1 : has_arrived j1 t := H_jobs_must_arrive_to_execute j1 t (by rw [scheduled_at_def, hsched_t]; simp)
          have hIN_j1 : j1 ∈ all_jobs := by
            apply arrived_between_implies_in_arrivals arr_seq H_arrival_times_are_consistent j1 0 (t1 + delta) hARR_j1
            exact ⟨Nat.zero_le _, Nat.lt_of_le_of_lt (by exact hHA_j1) ht.2⟩
          have hIN_f : j1 ∈ all_jobs.filter (fun j_hp => hep_job j_hp j) := by
            rw [List.mem_filter]; exact ⟨hIN_j1, hHEP_j1⟩
          have hSA_j1 : service_at sched j1 t = 1 := by
            rw [service_at_is_scheduled_at, scheduled_at_def, hsched_t]; simp
          have hHEP_sum : 1 ≤ ((all_jobs.filter fun j_hp => hep_job j_hp j).map fun j => service_at sched j t).sum :=
            le_trans (by rw [hSA_j1] : 1 ≤ service_at sched j1 t) (List.le_sum_of_mem (List.mem_map.mpr ⟨j1, hIN_f, rfl⟩))
          have hTOTAL_le : ((all_jobs.filter fun _ => true).map fun j => service_at sched j t).sum ≤ 1 := by
            have huniq : all_jobs.Nodup := arrivals_uniq arr_seq H_arrival_times_are_consistent H_arrival_sequence_is_a_set 0 (t1 + delta)
            exact service_of_jobs_le_1 arr_seq H_arrival_times_are_consistent sched H_jobs_come_from_arrival_sequence
              H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute (fun _ => true) all_jobs huniq t
          simp only [work, instant, hsched_t, hPI] at *; omega
        · -- j1 is not hep: prio_inv = 1
          push_neg at hHEP_j1
          have hPI : ((!hep_job j1 j).toNat) = 1 := by
            simp only [Bool.not_eq_true] at hHEP_j1
            simp [hHEP_j1]
          have hTOTAL_le : ((all_jobs.filter fun _ => true).map fun j => service_at sched j t).sum ≤ 1 := by
            have huniq : all_jobs.Nodup := arrivals_uniq arr_seq H_arrival_times_are_consistent H_arrival_sequence_is_a_set 0 (t1 + delta)
            exact service_of_jobs_le_1 arr_seq H_arrival_times_are_consistent sched H_jobs_come_from_arrival_sequence
              H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute (fun _ => true) all_jobs huniq t
          simp only [work, instant, hsched_t, hPI] at *; omega
    -- Step 2: combine hDECOMP with hHEP, hTOTAL and hCPI_le
    calc delta
        = service_of_jobs sched (fun _ => true) all_jobs t1 (t1 + delta) := hTOTAL.symm
      _ ≤ cumulative_priority_inversion sched j t1 (t1 + delta) +
          service_of_higher_or_equal_priority_jobs sched all_jobs j t1 (t1 + delta) := hDECOMP
      _ = cumulative_priority_inversion sched j t1 (t1 + delta) +
          service_of_higher_or_equal_priority_jobs sched t1_jobs j t1 (t1 + delta) := by
          rw [← hHEP]
      _ ≤ priority_inversion_bound +
          service_of_higher_or_equal_priority_jobs sched t1_jobs j t1 (t1 + delta) :=
          Nat.add_le_add_right hCPI_le _

include H_arrival_times_are_consistent H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_from_arrival_sequence H_job_task H_job_cost_positive H_work_conserving H_arrival_sequence_is_a_set H_priority_is_reflexive H_priority_is_transitive H_j_is_pending H_is_busy_prefix H_priority_inversion_is_bounded H_delta_positive H_workload_is_bounded H_no_quiet_time in
theorem busy_interval_too_much_workload :
    workload_of_higher_or_equal_priority_jobs j (arrivals_between arr_seq t1 (t1 + delta)) >
    service_of_higher_or_equal_priority_jobs
      sched (arrivals_between arr_seq t1 (t1 + delta)) j t1 (t1 + delta) := by
  -- Get the quiet time at t1 from the busy prefix
  obtain ⟨_, hQT, _, _⟩ := H_is_busy_prefix
  -- t1 + delta is not quiet
  have hNQ_delta : ¬ quiet_time arr_seq sched j (t1 + delta) := by
    exact H_no_quiet_time (t1 + delta) ⟨Nat.lt_add_of_pos_right H_delta_positive, le_rfl⟩
  -- There exists a pending hep job j0 at t1 + delta
  have hPEND := not_quiet_implies_exists_pending_job arr_seq
    H_arrival_times_are_consistent sched H_jobs_come_from_arrival_sequence
    H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute tsk j
    H_from_arrival_sequence H_job_task H_job_cost_positive t1 (t1 + delta)
    (Nat.le_add_right _ _) hQT hNQ_delta
  obtain ⟨j0, hARR0, ⟨hGE0, hLT0⟩, hHP0, hNOTCOMP0⟩ := hPEND
  -- j0 is in arrivals_between t1 (t1 + delta)
  set l := arrivals_between arr_seq t1 (t1 + delta) with hl_def
  have hIN0 : j0 ∈ l :=
    arrived_between_implies_in_arrivals arr_seq H_arrival_times_are_consistent j0 t1 (t1 + delta)
      hARR0 ⟨hGE0, hLT0⟩
  -- For all hep jobs in l: service ≤ cost
  have hSLE : ∀ j', j' ∈ l → hep_job j' j = true →
      service_during sched j' t1 (t1 + delta) ≤ job_cost j' :=
    fun j' _ _ => cumulative_service_le_job_cost sched H_completed_jobs_dont_execute j'
      ideal_proc_model_provides_unit_service t1 (t1 + delta)
  -- For j0: service < cost (since not completed)
  have hSLT0 : service_during sched j0 t1 (t1 + delta) < job_cost j0 := by
    unfold completed_by at hNOTCOMP0
    push_neg at hNOTCOMP0
    have hcat := service_cat sched j0 t1 (t1 + delta) (Nat.le_add_right _ _)
    have hcost_bound := service_at_most_cost sched H_completed_jobs_dont_execute j0
      ideal_proc_model_provides_unit_service (t1 + delta)
    simp only [work, instant] at *; omega
  -- service ≤ workload by term-by-term comparison
  have hLE := Prosa.Util.Sum.leq_sum_seq l (fun j_hp => hep_job j_hp j)
    (fun j' => service_during sched j' t1 (t1 + delta))
    (fun j' => job_cost j')
    hSLE
  -- Workload ≠ service (because j0 has strict inequality)
  have hNE : workload_of_jobs (fun j_hp => hep_job j_hp j) l ≠
      service_of_jobs sched (fun j_hp => hep_job j_hp j) l t1 (t1 + delta) := by
    intro hEQ
    -- If workload = service, then for every hep job, service = cost
    have hEQ_j0 := Prosa.Util.Sum.sum_majorant_eqn l
      (fun j' => service_during sched j' t1 (t1 + delta))
      (fun j' => job_cost j')
      (fun j_hp => hep_job j_hp j)
      hSLE
      (by unfold workload_of_jobs service_of_jobs at hEQ; exact hEQ.symm)
      j0 hIN0 hHP0
    -- But for j0, service < cost - contradiction
    simp only [work, instant] at hEQ_j0 hSLT0; omega
  unfold workload_of_higher_or_equal_priority_jobs service_of_higher_or_equal_priority_jobs
  show workload_of_jobs (fun j_hp => hep_job j_hp j) l >
    service_of_jobs sched (fun j_hp => hep_job j_hp j) l t1 (t1 + delta)
  unfold workload_of_jobs service_of_jobs
  unfold workload_of_jobs service_of_jobs at hNE
  exact Nat.lt_of_le_of_ne hLE (Ne.symm hNE)

include H_arrival_times_are_consistent H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_from_arrival_sequence H_job_task H_job_cost_positive H_work_conserving H_arrival_sequence_is_a_set H_priority_is_reflexive H_priority_is_transitive H_j_is_pending H_is_busy_prefix H_priority_inversion_is_bounded H_delta_positive H_workload_is_bounded H_no_quiet_time in
theorem busy_interval_workload_larger_than_interval :
    priority_inversion_bound +
      workload_of_higher_or_equal_priority_jobs j (arrivals_between arr_seq t1 (t1 + delta)) > delta := by
  have h1 : delta ≤ priority_inversion_bound +
      service_of_higher_or_equal_priority_jobs sched (arrivals_between arr_seq t1 (t1 + delta)) j t1 (t1 + delta) :=
    busy_interval_has_uninterrupted_service arr_seq H_arrival_times_are_consistent sched
      H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
      tsk j H_from_arrival_sequence H_job_task H_job_cost_positive H_work_conserving
      H_arrival_sequence_is_a_set H_priority_is_reflexive H_priority_is_transitive t_busy
      H_j_is_pending t1 H_is_busy_prefix priority_inversion_bound H_priority_inversion_is_bounded
      delta H_delta_positive H_workload_is_bounded H_no_quiet_time
  have h2 : workload_of_higher_or_equal_priority_jobs j (arrivals_between arr_seq t1 (t1 + delta)) >
      service_of_higher_or_equal_priority_jobs sched (arrivals_between arr_seq t1 (t1 + delta)) j t1 (t1 + delta) :=
    busy_interval_too_much_workload arr_seq H_arrival_times_are_consistent sched
      H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
      tsk j H_from_arrival_sequence H_job_task H_job_cost_positive H_work_conserving
      H_arrival_sequence_is_a_set H_priority_is_reflexive H_priority_is_transitive t_busy
      H_j_is_pending t1 H_is_busy_prefix priority_inversion_bound H_priority_inversion_is_bounded
      delta H_delta_positive H_workload_is_bounded H_no_quiet_time
  show priority_inversion_bound + workload_of_higher_or_equal_priority_jobs j (arrivals_between arr_seq t1 (t1 + delta)) > delta
  have h1' := h1
  have h2' := h2
  exact Nat.lt_of_le_of_lt h1' (Nat.add_lt_add_left h2' _)

end CannotBeBusyForSoLong

include H_arrival_times_are_consistent H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_from_arrival_sequence H_job_task H_job_cost_positive H_work_conserving H_arrival_sequence_is_a_set H_priority_is_reflexive H_priority_is_transitive H_j_is_pending H_is_busy_prefix H_priority_inversion_is_bounded H_delta_positive H_workload_is_bounded in
theorem busy_interval_is_bounded :
    ∃ t2,
      t2 ≤ t1 + delta ∧
      busy_interval arr_seq sched j t1 t2 := by
  have hPREFIX := H_is_busy_prefix
  obtain ⟨hLT, hQT, hNQ, hREL_le, hREL_lt⟩ := H_is_busy_prefix
  -- Case split: is there a quiet time t2 ∈ (t1, t1 + delta]?
  by_cases hEX : ∃ t2, t1 < t2 ∧ t2 ≤ t1 + delta ∧ quiet_time arr_seq sched j t2
  · -- There exists a quiet time. Find the minimum.
    -- Use Nat.find on the predicate
    have hEX' : ∃ t2, t1 < t2 ∧ t2 ≤ t1 + delta ∧ quiet_time arr_seq sched j t2 := hEX
    -- Take the minimum such t2
    -- We'll use Nat.find on the predicate "t1 < t ∧ t ≤ t1 + delta ∧ quiet_time t"
    have hEX_dec : ∃ n, t1 < n ∧ n ≤ t1 + delta ∧ quiet_time_dec arr_seq sched j n = true := by
      obtain ⟨t2, hgt, hle, hq⟩ := hEX'
      exact ⟨t2, hgt, hle, (quiet_time_P arr_seq H_arrival_times_are_consistent sched j t2).mpr hq⟩
    set t2 := Nat.find hEX_dec with ht2_def
    have hSPEC := Nat.find_spec hEX_dec
    have hGT : t1 < t2 := hSPEC.1
    have hLE : t2 ≤ t1 + delta := hSPEC.2.1
    have hQUIET2 : quiet_time arr_seq sched j t2 :=
      (quiet_time_P arr_seq H_arrival_times_are_consistent sched j t2).mp hSPEC.2.2
    -- Show t2 is the minimum
    have hMIN : ∀ t', t1 < t' ∧ t' ≤ t1 + delta ∧ quiet_time_dec arr_seq sched j t' = true → t2 ≤ t' := by
      intro t' ht'
      exact Nat.find_min' hEX_dec ht'
    -- Now show no quiet time in (t1, t2)
    have hNQT2 : ∀ t, t1 < t ∧ t < t2 → ¬ quiet_time arr_seq sched j t := by
      intro t ⟨hgt_t, hlt_t⟩ hq_t
      have hle_t : t ≤ t1 + delta := Nat.le_trans (Nat.le_of_lt hlt_t) hLE
      have hdec_t := (quiet_time_P arr_seq H_arrival_times_are_consistent sched j t).mpr hq_t
      have hmin := hMIN t ⟨hgt_t, hle_t, hdec_t⟩
      exact absurd hlt_t (Nat.not_lt.mpr hmin)
    -- Show j arrives in [t1, t2) and construct the busy interval
    -- First show job_arrival j ≤ t_busy (from hREL_lt : job_arrival j < t_busy + 1)
    have hJA_le_tbusy : job_arrival j ≤ t_busy := Nat.lt_succ_iff.mp hREL_lt
    -- Show t_busy < t2 by contradiction: if t2 ≤ t_busy, then t2 ∈ (t1, t_busy+1)
    -- and quiet_time t2, contradicting hNQ
    have htbusy_lt_t2 : t_busy < t2 := by
      by_contra hle
      push_neg at hle
      -- t2 ≤ t_busy, so t2 < t_busy + 1
      have ht2_lt : t2 < t_busy + 1 := Nat.lt_succ_of_le hle
      -- t2 ∈ (t1, t_busy+1), and quiet_time t2, contradicting hNQ
      exact hNQ t2 ⟨hGT, ht2_lt⟩ hQUIET2
    have hREL_lt2 : job_arrival j < t2 := Nat.lt_of_le_of_lt hJA_le_tbusy htbusy_lt_t2
    exact ⟨t2, hLE, ⟨hGT, hQT, hNQT2, hREL_le, hREL_lt2⟩, hQUIET2⟩
  · -- No quiet time in (t1, t1 + delta]. Derive contradiction.
    push_neg at hEX
    -- hEX : ∀ t2, t1 < t2 → t2 ≤ t1 + delta → ¬ quiet_time arr_seq sched j t2
    have hALL : ∀ t, t1 < t ∧ t ≤ t1 + delta → ¬ quiet_time arr_seq sched j t :=
      fun t ⟨hgt, hle⟩ => hEX t hgt hle
    exfalso
    have hTOOMUCH : priority_inversion_bound +
        workload_of_higher_or_equal_priority_jobs j (arrivals_between arr_seq t1 (t1 + delta)) > delta :=
      busy_interval_workload_larger_than_interval arr_seq H_arrival_times_are_consistent
        sched H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
        tsk j H_from_arrival_sequence H_job_task H_job_cost_positive H_work_conserving
        H_arrival_sequence_is_a_set H_priority_is_reflexive H_priority_is_transitive t_busy
        H_j_is_pending t1 hPREFIX priority_inversion_bound H_priority_inversion_is_bounded
        delta H_delta_positive H_workload_is_bounded hALL
    simp only [work, instant] at hTOOMUCH H_workload_is_bounded; omega

end UpperBound

end BoundingBusyInterval'

section BusyIntervalFromWorkloadBound

variable (priority_inversion_bound : duration)
variable (H_priority_inversion_is_bounded :
  priority_inversion_of_job_is_bounded_by arr_seq sched j priority_inversion_bound)

variable (delta : duration)
variable (H_delta_positive : delta > 0)
variable (H_workload_is_bounded :
  ∀ t, priority_inversion_bound +
    workload_of_higher_or_equal_priority_jobs j (arrivals_between arr_seq t (t + delta)) ≤ delta)

variable (H_positive_cost : job_cost j > 0)

include H_arrival_times_are_consistent H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_from_arrival_sequence H_job_task H_job_cost_positive H_work_conserving H_arrival_sequence_is_a_set H_priority_is_reflexive H_priority_is_transitive H_priority_inversion_is_bounded H_delta_positive H_workload_is_bounded H_positive_cost in
theorem exists_busy_interval :
    ∃ t1 t2,
      t1 ≤ job_arrival j ∧ job_arrival j < t2 ∧
      t2 ≤ t1 + delta ∧
      busy_interval arr_seq sched j t1 t2 := by
  -- Step 1: Show j is pending at its arrival time
  have hPEND : pending sched j (job_arrival j) :=
    job_pending_at_arrival sched j H_job_cost_positive H_jobs_must_arrive_to_execute
  -- Step 2: Get a busy interval prefix using exists_busy_interval_prefix
  have hPREFIX := exists_busy_interval_prefix arr_seq H_arrival_times_are_consistent sched
    H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
    j H_from_arrival_sequence H_job_cost_positive H_work_conserving
    H_arrival_sequence_is_a_set H_priority_is_reflexive
    (job_arrival j) hPEND
  obtain ⟨t1, hPrefix, hGE1, hGEarr⟩ := hPREFIX
  -- Step 3: Use busy_interval_is_bounded to get the upper bound
  have hBOUNDED := busy_interval_is_bounded arr_seq H_arrival_times_are_consistent sched
    H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
    tsk j H_from_arrival_sequence H_job_task H_job_cost_positive H_work_conserving
    H_arrival_sequence_is_a_set H_priority_is_reflexive H_priority_is_transitive
    (job_arrival j) hPEND t1 hPrefix priority_inversion_bound H_priority_inversion_is_bounded
    delta H_delta_positive (H_workload_is_bounded t1)
  obtain ⟨t2, hGE2, hBUSY⟩ := hBOUNDED
  -- Step 4: Show job_arrival j < t2
  refine ⟨t1, t2, hGE1, ?_, hGE2, hBUSY⟩
  -- Need: job_arrival j < t2
  by_contra hBUG
  push_neg at hBUG
  -- hBUG : t2 ≤ job_arrival j
  -- From hBUSY: busy_interval t1 t2 = (prefix, quiet_time t2)
  obtain ⟨⟨hLT12, _, hNOTQUIET, _, _⟩, hQUIET_t2⟩ := hBUSY
  -- From hPrefix: no quiet time in (t1, job_arrival j + 1)
  obtain ⟨_, _, hNQT_prefix, _, hREL_lt⟩ := hPrefix
  -- t2 ∈ (t1, job_arrival j + 1) since t1 < t2 and t2 ≤ job_arrival j < job_arrival j + 1
  have ht2_range : t1 < t2 ∧ t2 < job_arrival j + 1 := ⟨hLT12, Nat.lt_succ_of_le hBUG⟩
  exact hNQT_prefix t2 ht2_range hQUIET_t2

end BusyIntervalFromWorkloadBound

section ResponseTimeBoundFromBusyInterval

variable (priority_inversion_bound : duration)
variable (H_priority_inversion_is_bounded :
  priority_inversion_of_job_is_bounded_by arr_seq sched j priority_inversion_bound)

variable (delta : duration)
variable (H_delta_positive : delta > 0)
variable (H_workload_is_bounded :
  ∀ t, priority_inversion_bound +
    workload_of_higher_or_equal_priority_jobs j (arrivals_between arr_seq t (t + delta)) ≤ delta)

include H_arrival_times_are_consistent H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_from_arrival_sequence H_job_task H_job_cost_positive H_work_conserving H_arrival_sequence_is_a_set H_priority_is_reflexive H_priority_is_transitive H_priority_inversion_is_bounded H_delta_positive H_workload_is_bounded in
theorem busy_interval_bounds_response_time :
    completed_by sched j (job_arrival j + delta) := by
  -- Case split on whether job_cost j > 0
  by_cases hPOS : job_cost j > 0
  · -- Positive cost case: use exists_busy_interval
    have hBUSY := exists_busy_interval arr_seq H_arrival_times_are_consistent sched
      H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
      tsk j H_from_arrival_sequence H_job_task H_job_cost_positive H_work_conserving
      H_arrival_sequence_is_a_set H_priority_is_reflexive H_priority_is_transitive
      priority_inversion_bound H_priority_inversion_is_bounded delta H_delta_positive
      H_workload_is_bounded hPOS
    obtain ⟨t1, t2, hGE1, hLT2, hGE2, hBUSY⟩ := hBUSY
    -- t2 ≤ t1 + delta ≤ job_arrival j + delta
    have hLE : t2 ≤ job_arrival j + delta :=
      Nat.le_trans hGE2 (Nat.add_le_add_right hGE1 delta)
    -- j completes within the busy interval
    have hCOMP := job_completes_within_busy_interval arr_seq
      H_arrival_times_are_consistent sched H_jobs_come_from_arrival_sequence
      H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute tsk j
      H_from_arrival_sequence H_job_task H_job_cost_positive H_priority_is_reflexive t1 t2 hBUSY
    exact completion_monotonic sched j t2 (job_arrival j + delta) hLE hCOMP
  · -- Zero cost case: completed_by is trivially true
    push_neg at hPOS
    have hZERO : job_cost j = 0 := Nat.le_zero.mp hPOS
    unfold completed_by service
    simp only [work] at hZERO ⊢
    omega

end ResponseTimeBoundFromBusyInterval

end BoundingBusyInterval

end ExistsBusyIntervalJLFP

end Prosa.Analysis.Facts.Busy_interval.Busy_interval
