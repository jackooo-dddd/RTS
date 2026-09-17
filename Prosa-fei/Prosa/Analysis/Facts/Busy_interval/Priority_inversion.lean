-- Translated from: ../rt-proofs/analysis/facts/busy_interval/priority_inversion.v
import Prosa.Model.Task.Preemption.Parameters
import Prosa.Model.Schedule.Priority_driven
import Prosa.Model.Schedule.Work_conserving
import Prosa.Analysis.Definitions.Job_properties
import Prosa.Analysis.Definitions.Busy_interval
import Prosa.Analysis.Facts.Model.Ideal_schedule
import Prosa.Analysis.Facts.Busy_interval.Busy_interval
import Prosa.Model.Processor.Ideal
import Prosa.Model.Readiness.Basic

namespace Prosa.Analysis.Facts.Busy_interval.Priority_inversion

open Prosa.Behavior.Job
open Prosa.Behavior.Time
open Prosa.Behavior.Service
open Prosa.Behavior.Schedule
open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Ready
open Prosa.Model.Task.Concept
open Prosa.Model.Preemption.Parameter
open Prosa.Model.Priority.Classes
open Prosa.Model.Schedule.Preemption_time
open Prosa.Model.Schedule.Priority_driven
open Prosa.Model.Schedule.Work_conserving
open Prosa.Analysis.Definitions.Job_properties
open Prosa.Analysis.Definitions.Busy_interval
open Prosa.Analysis.Facts.Model.Ideal_schedule
open Prosa.Analysis.Facts.Busy_interval.Busy_interval
open Prosa.Model.Processor.Ideal
open Prosa.Model.Readiness.Basic
open Prosa.Model.Task.Preemption.Parameters
open Prosa.Util.Epsilon
open Prosa.Util.Minmax

attribute [local instance] pstate_instance
attribute [local instance] basic_ready_instance

section PreemptionTimes

variable {Task : TaskType}
variable [TaskCost Task]
variable [TaskMaxNonpreemptiveSegment Task]

variable {Job : JobType}
variable [DecidableEq Job]
variable [JobTask Job Task]
variable [JobArrival Job]
variable [JobCost Job]

variable [JobPreemptable Job]

variable (arr_seq : arrival_sequence Job)
variable (H_arrival_times_are_consistent : consistent_arrival_times arr_seq)

variable (sched : schedule (processor_state Job))
variable (H_jobs_come_from_arrival_sequence :
    jobs_come_from_arrival_sequence sched arr_seq)

variable (H_model_with_bounded_nonpreemptive_segments :
    valid_model_with_bounded_nonpreemptive_segments (Task := Task) arr_seq sched)

include H_arrival_times_are_consistent H_jobs_come_from_arrival_sequence
  H_model_with_bounded_nonpreemptive_segments

theorem zero_is_pt :
    preemption_time sched 0 = true := by
  unfold preemption_time
  split
  · next j h =>
    have h_arr : arrives_in arr_seq j :=
      H_jobs_come_from_arrival_sequence j 0 (by
        rw [Prosa.Analysis.Facts.Model.Ideal_schedule.scheduled_at_def]; simp [h])
    have h_serv : service sched j 0 = 0 := by
      simp [service, service_during]
    have h_preempt := (H_model_with_bounded_nonpreemptive_segments.1 j h_arr).1
    rw [h_serv]; exact h_preempt
  · rfl

theorem first_moment_is_pt :
    forall j prt,
      arrives_in arr_seq j ->
      ¬(scheduled_at sched j prt = true) ->
      scheduled_at sched j (prt + 1) = true ->
      preemption_time sched (prt + 1) = true := by
  intro j prt h_arr h_not_sched h_sched
  have h_eq : sched (prt + 1) = some j := by
    rw [Prosa.Analysis.Facts.Model.Ideal_schedule.scheduled_at_def] at h_sched
    exact of_decide_eq_true h_sched
  have h_exec_starts := (H_model_with_bounded_nonpreemptive_segments.1 j h_arr).2.2.2
  have h_preempt := h_exec_starts prt h_not_sched h_sched
  unfold preemption_time; rw [h_eq]; exact h_preempt

end PreemptionTimes

section PriorityInversionIsBounded

variable {Task : TaskType}
variable [TaskCost Task]

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
variable (H_priority_is_reflexive : reflexive_priorities (Job := Job))
variable (H_priority_is_transitive : transitive_priorities (Job := Job))

attribute [local instance] JLFP_to_JLDP

variable [TaskMaxNonpreemptiveSegment Task]
variable [JobPreemptable Job]

variable (H_valid_model_with_bounded_nonpreemptive_segments :
    valid_model_with_bounded_nonpreemptive_segments (Task := Task) arr_seq sched)

variable (H_work_conserving : work_conserving arr_seq sched)

variable (H_respects_policy :
    respects_policy_at_preemption_point arr_seq sched)

include H_arrival_times_are_consistent H_jobs_come_from_arrival_sequence
  H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
  H_priority_is_reflexive H_priority_is_transitive
  H_valid_model_with_bounded_nonpreemptive_segments
  H_work_conserving H_respects_policy

noncomputable def max_length_of_priority_inversion (j : Job) (t : instant) : Nat :=
  bigMaxListCond (arrivals_before arr_seq t)
    (fun j_lp => ¬(hep_job j_lp j = true))
    (fun j_lp => job_max_nonpreemptive_segment j_lp - ε)

variable (j : Job)
variable (H_j_arrives : arrives_in arr_seq j)
variable (H_job_cost_positive : job_cost_positive j)

variable (t1 t2 : instant)
variable (H_busy_interval_prefix :
    busy_interval_prefix arr_seq sched j t1 t2)

section PreemptionTimeAndPriorityInversion

section ProcessorBusyWithHEPJobAtPreemptionPoints

variable (t : instant)
variable (H_t_in_busy_interval : t1 <= t /\ t < t2)
variable (H_t_preemption_time : preemption_time sched t = true)

include H_j_arrives H_job_cost_positive H_busy_interval_prefix
  H_t_in_busy_interval H_t_preemption_time

theorem instant_t_is_not_idle :
    ¬is_idle sched t := by
  intro h_idle
  obtain ⟨h_le, h_lt⟩ := H_t_in_busy_interval
  obtain ⟨h_pos, h_qt1, h_nqt, h_arr_le, h_arr_lt⟩ := H_busy_interval_prefix
  have h_idle' : sched t = none := h_idle
  -- Any pending job in arr_seq at t gives contradiction: backlogged → work_conserving → scheduled → ¬idle
  suffices ∃ (j' : Job), arrives_in arr_seq j' ∧ pending sched j' t by
    obtain ⟨j', h_arr_j', h_pend⟩ := this
    have h_nsched : scheduled_at sched j' t = false := by
      simp only [scheduled_at, Prosa.Analysis.Facts.Model.Ideal_schedule.scheduled_in_def]
      rw [h_idle']; simp
    have h_bl : backlogged sched j' t = true := by
      simp only [backlogged, Bool.and_eq_true, Bool.not_eq_true_eq_eq_false]
      refine ⟨?_, h_nsched⟩
      show job_ready sched j' t = true
      simp only [JobReady.job_ready,
        Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true_eq_eq_false, decide_eq_false_iff_not]
      exact h_pend
    obtain ⟨_, h_jo⟩ := H_work_conserving j' t h_arr_j' h_bl
    simp only [scheduled_at, Prosa.Analysis.Facts.Model.Ideal_schedule.scheduled_in_def] at h_jo
    rw [h_idle'] at h_jo; simp at h_jo
  -- Find a pending job at t
  by_cases h_gt : t1 < t
  · -- t ∈ (t1, t2): ¬quiet at t gives a witness
    have h_nq := h_nqt t ⟨h_gt, h_lt⟩
    simp only [quiet_time] at h_nq; push_neg at h_nq
    obtain ⟨j_hp, h_arr_hp, _, h_before_hp, h_ncompl_hp⟩ := h_nq
    have h_has_arr : has_arrived j_hp t := by
      unfold has_arrived; unfold arrived_before at h_before_hp; exact Nat.le_of_lt h_before_hp
    exact ⟨j_hp, h_arr_hp, h_has_arr, h_ncompl_hp⟩
  · -- t = t1
    push_neg at h_gt
    have h_eq : t = t1 := by simp only [instant, duration] at *; omega
    by_cases h_arr_eq : job_arrival j = t1
    · -- j arrives exactly at t = t1; service = 0 but cost > 0, so j is pending
      have h_serv := Prosa.Analysis.Facts.Behavior.Service.no_service_before_arrival
        sched j H_jobs_must_arrive_to_execute t (by rw [h_arr_eq, h_eq])
      have h_has_arr : has_arrived j t := by
        unfold has_arrived; simp only [instant, duration] at *; omega
      have h_not_compl : ¬ completed_by sched j t := by
        unfold completed_by; rw [h_serv]; exact not_le.mpr H_job_cost_positive
      exact ⟨j, H_j_arrives, h_has_arr, h_not_compl⟩
    · -- j arrives after t1; use ¬quiet at t1+1
      have h_arr_gt : t1 < job_arrival j := Nat.lt_of_le_of_ne h_arr_le (Ne.symm h_arr_eq)
      by_cases h_t1p1 : t1 + 1 < t2
      · have h_nq := h_nqt (t1 + 1) ⟨by simp only [instant, duration] at *; omega, h_t1p1⟩
        simp only [quiet_time] at h_nq; push_neg at h_nq
        obtain ⟨j_hp, h_arr_hp, _, h_before_hp, h_ncompl_hp⟩ := h_nq
        have h_has_arr : has_arrived j_hp t := by
          unfold has_arrived; unfold arrived_before at h_before_hp
          simp only [instant, duration] at *; omega
        have h_ncompl_t : ¬ completed_by sched j_hp t := by
          intro hc
          exact h_ncompl_hp (Prosa.Analysis.Facts.Behavior.Completion.completion_monotonic sched j_hp t (t1 + 1)
            (by simp only [instant, duration] at *; omega) hc)
        exact ⟨j_hp, h_arr_hp, h_has_arr, h_ncompl_t⟩
      · -- t1+1 ≥ t2 but job_arrival j > t1 and job_arrival j < t2 → contradiction
        simp only [instant, duration] at *; omega

theorem t_lt_t2_or_t_eq_t2 :
    t < t2 - 1 \/ t = t2 - 1 := by
  obtain ⟨_, h_lt⟩ := H_t_in_busy_interval
  obtain ⟨h_pos, _⟩ := H_busy_interval_prefix
  simp only [instant, duration] at *
  omega

theorem scheduled_at_preemption_time_implies_higher_or_equal_priority :
    forall (jhp : Job),
      scheduled_at sched jhp t = true ->
      hep_job jhp j = true := by
  intro jhp h_sched
  obtain ⟨h_le, h_lt⟩ := H_t_in_busy_interval
  obtain ⟨h_pos, h_qt1, h_nqt, h_arr_le, h_arr_lt⟩ := H_busy_interval_prefix
  -- Find j' with hep_job j' j, arrived at t, not completed at t
  suffices ∃ (j' : Job), arrives_in arr_seq j' ∧ hep_job j' j = true ∧
      has_arrived j' t ∧ ¬completed_by sched j' t by
    obtain ⟨j', h_arr_j', h_hep_j', h_has_arr, h_ncompl⟩ := this
    by_cases h_eq : j' = jhp
    · exact h_eq ▸ h_hep_j'
    · -- j' ≠ jhp: j' not scheduled at t (uniprocessor), so backlogged
      have h_some_jhp : sched t = some jhp := by
        rw [scheduled_at_def] at h_sched; exact of_decide_eq_true h_sched
      have h_nsched_j' : scheduled_at sched j' t = false := by
        simp only [scheduled_at, Prosa.Analysis.Facts.Model.Ideal_schedule.scheduled_in_def]
        rw [h_some_jhp]; simp [Ne.symm h_eq]
      have h_bl : backlogged sched j' t = true := by
        simp only [backlogged, Bool.and_eq_true, Bool.not_eq_true_eq_eq_false]
        refine ⟨?_, h_nsched_j'⟩
        show job_ready sched j' t = true
        simp only [JobReady.job_ready,
          Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true_eq_eq_false,
          decide_eq_false_iff_not]
        exact ⟨h_has_arr, h_ncompl⟩
      have h_resp := H_respects_policy j' jhp t h_arr_j' H_t_preemption_time h_bl h_sched
      exact H_priority_is_transitive t jhp j' j h_resp h_hep_j'
  -- Find the hep witness
  by_cases h_gt : t1 < t
  · -- ¬quiet at t
    have h_nq := h_nqt t ⟨h_gt, h_lt⟩
    simp only [quiet_time] at h_nq; push_neg at h_nq
    obtain ⟨j', h_arr_j', h_hep_j', h_before_j', h_ncompl_j'⟩ := h_nq
    exact ⟨j', h_arr_j', h_hep_j',
      by unfold has_arrived; unfold arrived_before at h_before_j'; exact Nat.le_of_lt h_before_j',
      h_ncompl_j'⟩
  · push_neg at h_gt
    have h_teq : t = t1 := by simp only [instant, duration] at *; omega
    by_cases h_arr_eq : job_arrival j = t1
    · -- j arrives at t = t1
      have h_serv := Prosa.Analysis.Facts.Behavior.Service.no_service_before_arrival
        sched j H_jobs_must_arrive_to_execute t (by rw [h_arr_eq, h_teq])
      exact ⟨j, H_j_arrives, H_priority_is_reflexive 0 j,
        by unfold has_arrived; simp only [instant, duration] at *; omega,
        by unfold completed_by; rw [h_serv]; exact not_le.mpr H_job_cost_positive⟩
    · have h_arr_gt : t1 < job_arrival j := Nat.lt_of_le_of_ne h_arr_le (Ne.symm h_arr_eq)
      by_cases h_t1p1 : t1 + 1 < t2
      · have h_nq := h_nqt (t1 + 1) ⟨by simp only [instant, duration] at *; omega, h_t1p1⟩
        simp only [quiet_time] at h_nq; push_neg at h_nq
        obtain ⟨j', h_arr_j', h_hep_j', h_before_j', h_ncompl_j'⟩ := h_nq
        have h_has_arr : has_arrived j' t := by
          unfold has_arrived; unfold arrived_before at h_before_j'
          simp only [instant, duration] at *; omega
        have h_ncompl_t : ¬ completed_by sched j' t := by
          intro hc
          exact h_ncompl_j' (Prosa.Analysis.Facts.Behavior.Completion.completion_monotonic
            sched j' t (t1 + 1) (by simp only [instant, duration] at *; omega) hc)
        exact ⟨j', h_arr_j', h_hep_j', h_has_arr, h_ncompl_t⟩
      · exfalso; simp only [instant, duration] at *; omega

theorem scheduled_at_preemption_time_implies_higher_or_equal_priority_lt :
    t < t2 - 1 ->
    forall (jhp : Job),
      scheduled_at sched jhp t = true ->
      hep_job jhp j = true := by
  intro _ jhp h_sched
  exact scheduled_at_preemption_time_implies_higher_or_equal_priority
    arr_seq H_arrival_times_are_consistent sched H_jobs_come_from_arrival_sequence
    H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
    H_priority_is_reflexive H_priority_is_transitive
    H_valid_model_with_bounded_nonpreemptive_segments H_work_conserving H_respects_policy
    j H_j_arrives H_job_cost_positive t1 t2 H_busy_interval_prefix
    t H_t_in_busy_interval H_t_preemption_time jhp h_sched

theorem scheduled_at_preemption_time_implies_higher_or_equal_priority_eq :
    t = t2 - 1 ->
    forall (jhp : Job),
      scheduled_at sched jhp t = true ->
      hep_job jhp j = true := by
  intro _ jhp h_sched
  exact scheduled_at_preemption_time_implies_higher_or_equal_priority
    arr_seq H_arrival_times_are_consistent sched H_jobs_come_from_arrival_sequence
    H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
    H_priority_is_reflexive H_priority_is_transitive
    H_valid_model_with_bounded_nonpreemptive_segments H_work_conserving H_respects_policy
    j H_j_arrives H_job_cost_positive t1 t2 H_busy_interval_prefix
    t H_t_in_busy_interval H_t_preemption_time jhp h_sched

theorem scheduled_at_preemption_time_implies_arrived_between_within_busy_interval :
    forall (jhp : Job),
      scheduled_at sched jhp t = true ->
      arrived_between jhp t1 t2 := by
  intro jhp h_sched
  have h_hep : hep_job jhp j = true :=
    scheduled_at_preemption_time_implies_higher_or_equal_priority
      arr_seq H_arrival_times_are_consistent sched H_jobs_come_from_arrival_sequence
      H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
      H_priority_is_reflexive H_priority_is_transitive
      H_valid_model_with_bounded_nonpreemptive_segments H_work_conserving H_respects_policy
      j H_j_arrives H_job_cost_positive t1 t2 H_busy_interval_prefix
      t H_t_in_busy_interval H_t_preemption_time jhp h_sched
  obtain ⟨h_le, h_lt⟩ := H_t_in_busy_interval
  obtain ⟨_, h_qt1, _, _, _⟩ := H_busy_interval_prefix
  have h_arr := H_jobs_come_from_arrival_sequence jhp t h_sched
  have h_has_arrived := H_jobs_must_arrive_to_execute jhp t h_sched
  unfold arrived_between
  constructor
  · -- t1 ≤ job_arrival jhp
    by_contra h_neg
    push_neg at h_neg
    -- jhp arrived before t1 with hep → completed at t1 (quiet_time)
    have h_before : arrived_before jhp t1 := h_neg
    have h_compl_t1 := h_qt1 jhp h_arr h_hep h_before
    -- completed at t1 ≤ t → completed at t
    have h_compl_t := Prosa.Analysis.Facts.Behavior.Completion.completion_monotonic
      sched jhp t1 t h_le h_compl_t1
    -- but completed jobs don't execute, contradiction
    have h_cdj := H_completed_jobs_dont_execute jhp t h_sched
    unfold completed_by at h_compl_t; unfold work at *; omega
  · -- job_arrival jhp < t2
    unfold has_arrived at h_has_arrived
    simp only [instant, duration] at *; omega

theorem not_quiet_implies_exists_scheduled_hp_job_at_preemption_point :
    exists (j_hp : Job),
      arrived_between j_hp t1 t2 /\
      hep_job j_hp j = true /\
      scheduled_at sched j_hp t = true := by
  have h_not_idle := instant_t_is_not_idle
    arr_seq H_arrival_times_are_consistent sched H_jobs_come_from_arrival_sequence
    H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
    H_priority_is_reflexive H_priority_is_transitive
    H_valid_model_with_bounded_nonpreemptive_segments H_work_conserving H_respects_policy
    j H_j_arrives H_job_cost_positive t1 t2 H_busy_interval_prefix
    t H_t_in_busy_interval H_t_preemption_time
  -- processor not idle → sched t = some j_hp for some j_hp
  have h_exists : ∃ j_hp, sched t = some j_hp := by
    by_contra h_all_none
    push_neg at h_all_none
    exact h_not_idle (by show sched t = none; exact Option.eq_none_iff_forall_not_mem.mpr h_all_none)
  obtain ⟨j_hp, h_some⟩ := h_exists
  have h_sched : scheduled_at sched j_hp t = true := by
    rw [scheduled_at_def]; exact decide_eq_true h_some
  have h_arr_btwn : arrived_between j_hp t1 t2 :=
    scheduled_at_preemption_time_implies_arrived_between_within_busy_interval
      arr_seq H_arrival_times_are_consistent sched H_jobs_come_from_arrival_sequence
      H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
      H_priority_is_reflexive H_priority_is_transitive
      H_valid_model_with_bounded_nonpreemptive_segments H_work_conserving H_respects_policy
      j H_j_arrives H_job_cost_positive t1 t2 H_busy_interval_prefix
      t H_t_in_busy_interval H_t_preemption_time j_hp h_sched
  have h_hep2 : hep_job j_hp j = true :=
    scheduled_at_preemption_time_implies_higher_or_equal_priority
      arr_seq H_arrival_times_are_consistent sched H_jobs_come_from_arrival_sequence
      H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
      H_priority_is_reflexive H_priority_is_transitive
      H_valid_model_with_bounded_nonpreemptive_segments H_work_conserving H_respects_policy
      j H_j_arrives H_job_cost_positive t1 t2 H_busy_interval_prefix
      t H_t_in_busy_interval H_t_preemption_time j_hp h_sched
  exact ⟨j_hp, h_arr_btwn, h_hep2, h_sched⟩

end ProcessorBusyWithHEPJobAtPreemptionPoints

theorem scheduling_of_any_segment_starts_with_preemption_time :
    forall (j' : Job) (t' : instant),
      scheduled_at sched j' t' = true ->
      exists pt,
        job_arrival j' <= pt /\ pt <= t' /\
        preemption_time sched pt = true /\
        (forall t'', pt <= t'' -> t'' <= t' -> scheduled_at sched j' t'' = true) := by
  intro j' t'
  induction t' using Nat.strongRecOn with
  | ind t' ih =>
    intro h_sched
    cases t' with
    | zero =>
      refine ⟨0, ?_, le_refl _, ?_, ?_⟩
      · exact H_jobs_must_arrive_to_execute j' 0 h_sched
      · exact zero_is_pt arr_seq H_arrival_times_are_consistent sched
          H_jobs_come_from_arrival_sequence H_valid_model_with_bounded_nonpreemptive_segments
      · intro t'' h1 h2; have := Nat.le_antisymm h2 h1; subst this; exact h_sched
    | succ n =>
      by_cases h_prev : scheduled_at sched j' n = true
      · -- j' scheduled at n: extend from IH
        obtain ⟨pt, h1, h2, h3, h4⟩ := ih n (Nat.lt_succ_of_le (le_refl _)) h_prev
        refine ⟨pt, h1, Nat.le_succ_of_le h2, h3, ?_⟩
        intro t'' ht1 ht2
        rcases Nat.eq_or_lt_of_le ht2 with h_eq | h_lt
        · rw [h_eq]; exact h_sched
        · exact h4 t'' ht1 (Nat.lt_succ_iff.mp h_lt)
      · -- j' NOT scheduled at n: pt = n + 1
        have h_arr := H_jobs_come_from_arrival_sequence j' (n + 1) h_sched
        refine ⟨n + 1, ?_, le_refl _, ?_, ?_⟩
        · exact H_jobs_must_arrive_to_execute j' (n + 1) h_sched
        · exact first_moment_is_pt arr_seq H_arrival_times_are_consistent sched
            H_jobs_come_from_arrival_sequence H_valid_model_with_bounded_nonpreemptive_segments
            j' n h_arr h_prev h_sched
        · intro t'' h1 h2; have := Nat.le_antisymm h2 h1; subst this; exact h_sched

include H_j_arrives H_job_cost_positive H_busy_interval_prefix in
theorem not_quiet_implies_exists_scheduled_hp_job_after_preemption_point :
    forall tp t',
      preemption_time sched tp = true ->
      t1 <= tp /\ tp < t2 ->
      tp <= t' /\ t' < t2 ->
      exists (j_hp : Job),
        arrived_between j_hp t1 (t' + 1) /\
        hep_job j_hp j = true /\
        scheduled_at sched j_hp t' = true := by
  intro tp t' h_pp ⟨h_t1_le_tp, h_tp_lt_t2⟩ ⟨h_tp_le_t', h_t'_lt_t2⟩
  have h_t1_le_t' : t1 ≤ t' := le_trans h_t1_le_tp h_tp_le_t'
  -- Step 1: Show processor is not idle at t' (inline from not_quiet_implies_not_idle)
  have h_sched_exists : ∃ jhp, sched t' = some jhp := by
    by_contra h_all_none
    push_neg at h_all_none
    have h_idle : sched t' = none := Option.eq_none_iff_forall_not_mem.mpr h_all_none
    obtain ⟨_, h_qt1, h_nqt, h_arr_le, h_arr_lt⟩ := H_busy_interval_prefix
    suffices ∃ (j' : Job), arrives_in arr_seq j' ∧ pending sched j' t' by
      obtain ⟨j', h_arr_j', h_pend⟩ := this
      have h_nsched : scheduled_at sched j' t' = false := by
        rw [scheduled_at_def, h_idle]; rfl
      have h_bl : backlogged sched j' t' = true := by
        simp only [backlogged, Bool.and_eq_true, Bool.not_eq_true_eq_eq_false]
        refine ⟨?_, h_nsched⟩
        show job_ready sched j' t' = true
        simp only [JobReady.job_ready, Bool.and_eq_true, decide_eq_true_eq,
          Bool.not_eq_true_eq_eq_false, decide_eq_false_iff_not]
        exact ⟨h_pend.1, h_pend.2⟩
      obtain ⟨jo, h_sched_jo⟩ := H_work_conserving j' t' h_arr_j' h_bl
      rw [scheduled_at_def, h_idle] at h_sched_jo; simp at h_sched_jo
    by_cases h_gt : t1 < t'
    · have h_nq := h_nqt t' ⟨h_gt, h_t'_lt_t2⟩
      simp only [quiet_time] at h_nq; push_neg at h_nq
      obtain ⟨j_hp, h_arr_jhp, h_hep, h_before, h_ncompl⟩ := h_nq
      have h_has_arr : has_arrived j_hp t' := by
        unfold has_arrived; unfold arrived_before at h_before
        simp only [instant, duration] at *; omega
      exact ⟨j_hp, h_arr_jhp, h_has_arr, h_ncompl⟩
    · push_neg at h_gt
      have h_teq : t' = t1 := by simp only [instant, duration] at *; omega
      subst h_teq
      by_cases h_j_arr : job_arrival j = t'
      · have h_serv := Prosa.Analysis.Facts.Behavior.Service.no_service_before_arrival
          sched j H_jobs_must_arrive_to_execute t' (by rw [h_j_arr])
        exact ⟨j, H_j_arrives,
          by unfold has_arrived; simp only [instant, duration] at *; omega,
          by unfold completed_by; rw [h_serv]; exact not_le.mpr H_job_cost_positive⟩
      · have h_j_arr_gt : t' < job_arrival j := by
          simp only [instant, duration] at *; omega
        have h_tp1_lt : t' + 1 < t2 := by
          simp only [instant, duration] at *; omega
        have h_nq := h_nqt (t' + 1) ⟨by simp only [instant, duration] at *; omega, h_tp1_lt⟩
        simp only [quiet_time] at h_nq; push_neg at h_nq
        obtain ⟨j_hp, h_arr_jhp, h_hep, h_before, h_ncompl⟩ := h_nq
        have h_has_arr : has_arrived j_hp t' := by
          unfold has_arrived; unfold arrived_before at h_before
          simp only [instant, duration] at *; omega
        have h_ncompl_t' : ¬ completed_by sched j_hp t' := by
          intro hc
          exact h_ncompl (Prosa.Analysis.Facts.Behavior.Completion.completion_monotonic
            sched j_hp t' (t' + 1) (Nat.le_succ _) hc)
        exact ⟨j_hp, h_arr_jhp, h_has_arr, h_ncompl_t'⟩
  -- Step 2: Get the scheduled job
  obtain ⟨jhp, h_some⟩ := h_sched_exists
  have h_sched : scheduled_at sched jhp t' = true := by
    rw [scheduled_at_def]; exact decide_eq_true h_some
  -- Step 3: Show hep_job jhp j
  have h_hep : hep_job jhp j = true := by
    obtain ⟨prt, h_arr_prt, h_prt_le_t', h_pt, h_cont⟩ :=
      scheduling_of_any_segment_starts_with_preemption_time
        arr_seq H_arrival_times_are_consistent sched H_jobs_come_from_arrival_sequence
        H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
        H_priority_is_reflexive H_priority_is_transitive
        H_valid_model_with_bounded_nonpreemptive_segments H_work_conserving H_respects_policy
        jhp t' h_sched
    by_cases h_t1_le_prt : t1 ≤ prt
    · -- prt ≥ t1: in the busy interval
      have h_prt_lt_t2 : prt < t2 := lt_of_le_of_lt h_prt_le_t' h_t'_lt_t2
      obtain ⟨jlp, _, h_hep_jlp, h_sched_jlp⟩ :=
        not_quiet_implies_exists_scheduled_hp_job_at_preemption_point
          arr_seq H_arrival_times_are_consistent sched H_jobs_come_from_arrival_sequence
          H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
          H_priority_is_reflexive H_priority_is_transitive
          H_valid_model_with_bounded_nonpreemptive_segments H_work_conserving H_respects_policy
          j H_j_arrives H_job_cost_positive t1 t2 H_busy_interval_prefix
          prt ⟨h_t1_le_prt, h_prt_lt_t2⟩ h_pt
      have h_jhp_at_prt := h_cont prt (le_refl _) h_prt_le_t'
      have h_eq := ideal_proc_model_is_a_uniprocessor_model jhp jlp sched prt h_jhp_at_prt h_sched_jlp
      rw [h_eq]; exact h_hep_jlp
    · -- prt < t1: by contradiction
      push_neg at h_t1_le_prt
      by_contra h_nlp
      obtain ⟨jhp', _, h_hep_jhp', h_sched_jhp'⟩ :=
        not_quiet_implies_exists_scheduled_hp_job_at_preemption_point
          arr_seq H_arrival_times_are_consistent sched H_jobs_come_from_arrival_sequence
          H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
          H_priority_is_reflexive H_priority_is_transitive
          H_valid_model_with_bounded_nonpreemptive_segments H_work_conserving H_respects_policy
          j H_j_arrives H_job_cost_positive t1 t2 H_busy_interval_prefix
          tp ⟨h_t1_le_tp, h_tp_lt_t2⟩ h_pp
      have h_jhp_at_tp := h_cont tp (le_trans (le_of_lt h_t1_le_prt) h_t1_le_tp) h_tp_le_t'
      have h_eq := ideal_proc_model_is_a_uniprocessor_model jhp' jhp sched tp h_sched_jhp' h_jhp_at_tp
      rw [h_eq] at h_hep_jhp'
      exact h_nlp h_hep_jhp'
  -- Step 4: arrived_between
  refine ⟨jhp, ?_, h_hep, h_sched⟩
  constructor
  · -- t1 ≤ job_arrival jhp
    by_contra h_neg; push_neg at h_neg
    obtain ⟨_, h_qt1, _, _⟩ := H_busy_interval_prefix
    have h_arr_jhp := H_jobs_come_from_arrival_sequence jhp t' h_sched
    have h_compl_t1 := h_qt1 jhp h_arr_jhp h_hep h_neg
    have h_compl_t' := Prosa.Analysis.Facts.Behavior.Completion.completion_monotonic
      sched jhp t1 t' h_t1_le_t' h_compl_t1
    have h_cdj := H_completed_jobs_dont_execute jhp t' h_sched
    unfold completed_by at h_compl_t'; unfold work at *; omega
  · -- job_arrival jhp < t' + 1
    have h_has_arr := H_jobs_must_arrive_to_execute jhp t' h_sched
    unfold has_arrived at h_has_arr
    simp only [instant, duration] at *; omega

variable (K : duration)
variable (H_preemption_time_exists :
    exists pr_t, preemption_time sched pr_t = true /\ t1 <= pr_t /\ pr_t <= t1 + K)

include H_preemption_time_exists

include H_j_arrives H_job_cost_positive H_busy_interval_prefix in
theorem not_quiet_implies_exists_scheduled_hp_job :
    forall t',
      t1 + K <= t' /\ t' < t2 ->
      exists (j_hp : Job),
        arrived_between j_hp t1 (t' + 1) /\
        hep_job j_hp j = true /\
        scheduled_at sched j_hp t' = true := by
  intro t' ⟨h_ge, h_lt⟩
  obtain ⟨prt, h_pt, h_ge_prt, h_le_prt⟩ := H_preemption_time_exists
  exact not_quiet_implies_exists_scheduled_hp_job_after_preemption_point
    arr_seq H_arrival_times_are_consistent sched H_jobs_come_from_arrival_sequence
    H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
    H_priority_is_reflexive H_priority_is_transitive
    H_valid_model_with_bounded_nonpreemptive_segments H_work_conserving H_respects_policy
    j H_j_arrives H_job_cost_positive t1 t2 H_busy_interval_prefix
    prt t' h_pt
    ⟨h_ge_prt, by simp only [instant, duration] at *; omega⟩
    ⟨by simp only [instant, duration] at *; omega, h_lt⟩

end PreemptionTimeAndPriorityInversion

section PreemptionTimeExists

theorem hp_job_not_scheduled_before_quiet_time :
    forall jhp t',
      quiet_time arr_seq sched j (t' + 1) ->
      scheduled_at sched jhp (t' + 1) = true ->
      hep_job jhp j = true ->
      ¬(scheduled_at sched jhp t' = true) := by
  intro jhp t' h_quiet h_sched h_hep h_sched_t'
  -- jhp is scheduled at t'+1 → arrives in arr_seq
  have h_arr := H_jobs_come_from_arrival_sequence jhp (t' + 1) h_sched
  -- jhp has arrived at t'+1
  have h_has_arrived := H_jobs_must_arrive_to_execute jhp (t' + 1) h_sched
  -- jhp is not completed at t'+1 (completed_jobs_dont_execute)
  have h_not_compl : ¬ completed_by sched jhp (t' + 1) := by
    intro h_compl
    have := H_completed_jobs_dont_execute jhp (t' + 1) h_sched
    unfold completed_by at h_compl; unfold work at *; omega
  -- jhp didn't arrive before t'+1 (quiet time → completed → contradiction)
  have h_not_before : ¬ arrived_before jhp (t' + 1) := by
    intro h_before; exact h_not_compl (h_quiet jhp h_arr h_hep h_before)
  -- job_arrival jhp = t' + 1
  have h_arr_eq : job_arrival jhp = t' + 1 := by
    unfold has_arrived at h_has_arrived; unfold arrived_before at h_not_before
    simp only [instant, duration] at *; omega
  -- So jhp hasn't arrived at t'
  have h_not_arrived_t' : ¬ has_arrived jhp t' := by
    unfold has_arrived; rw [h_arr_eq]; simp only [instant, duration]; omega
  -- Since jhp isn't arrived at t', it can't be scheduled at t'
  exact h_not_arrived_t' (H_jobs_must_arrive_to_execute jhp t' h_sched_t')

include H_j_arrives H_job_cost_positive H_busy_interval_prefix in
theorem low_priority_job_arrives_before_busy_interval_prefix :
    forall jlp t',
      t1 <= t' /\ t' < t2 ->
      scheduled_at sched jlp t' = true ->
      ¬(hep_job jlp j = true) ->
      job_arrival jlp < t1 := by
  intro jlp t' ⟨h_ge, h_lt⟩ h_sched h_lp
  by_contra h_neg; push_neg at h_neg
  -- h_neg : t1 ≤ job_arrival jlp
  obtain ⟨pt, h_arr_le_pt, h_pt_le_t', h_pt_preempt, h_cont⟩ :=
    scheduling_of_any_segment_starts_with_preemption_time
      arr_seq H_arrival_times_are_consistent sched H_jobs_come_from_arrival_sequence
      H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
      H_priority_is_reflexive H_priority_is_transitive
      H_valid_model_with_bounded_nonpreemptive_segments H_work_conserving H_respects_policy
      jlp t' h_sched
  have h_t1_le_pt : t1 ≤ pt := le_trans h_neg h_arr_le_pt
  have h_pt_lt_t2 : pt < t2 := lt_of_le_of_lt h_pt_le_t' h_lt
  obtain ⟨jhp, _, h_hep_jhp, h_sched_jhp⟩ :=
    not_quiet_implies_exists_scheduled_hp_job_at_preemption_point
      arr_seq H_arrival_times_are_consistent sched H_jobs_come_from_arrival_sequence
      H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
      H_priority_is_reflexive H_priority_is_transitive
      H_valid_model_with_bounded_nonpreemptive_segments H_work_conserving H_respects_policy
      j (by exact H_j_arrives) (by exact H_job_cost_positive)
      t1 t2 (by exact H_busy_interval_prefix)
      pt ⟨h_t1_le_pt, h_pt_lt_t2⟩ h_pt_preempt
  have h_jlp_at_pt := h_cont pt (le_refl _) h_pt_le_t'
  have h_eq := ideal_proc_model_is_a_uniprocessor_model jlp jhp sched pt h_jlp_at_pt h_sched_jhp
  rw [h_eq] at h_lp; exact h_lp h_hep_jhp

include H_j_arrives H_job_cost_positive H_busy_interval_prefix in
theorem low_priority_job_scheduled_before_busy_interval_prefix :
    forall jlp t',
      t1 <= t' /\ t' < t2 ->
      scheduled_at sched jlp t' = true ->
      ¬(hep_job jlp j = true) ->
      exists t'', t'' < t1 /\ scheduled_at sched jlp t'' = true := by
  intro jlp t' ⟨h_ge, h_lt⟩ h_sched h_lp
  have h_arr_lt := low_priority_job_arrives_before_busy_interval_prefix
    arr_seq H_arrival_times_are_consistent sched H_jobs_come_from_arrival_sequence
    H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
    H_priority_is_reflexive H_priority_is_transitive
    H_valid_model_with_bounded_nonpreemptive_segments H_work_conserving H_respects_policy
    j H_j_arrives H_job_cost_positive t1 t2 H_busy_interval_prefix
    jlp t' ⟨h_ge, h_lt⟩ h_sched h_lp
  obtain ⟨pt, h_arr_le_pt, h_pt_le_t', h_pt_preempt, h_cont⟩ :=
    scheduling_of_any_segment_starts_with_preemption_time
      arr_seq H_arrival_times_are_consistent sched H_jobs_come_from_arrival_sequence
      H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
      H_priority_is_reflexive H_priority_is_transitive
      H_valid_model_with_bounded_nonpreemptive_segments H_work_conserving H_respects_policy
      jlp t' h_sched
  -- pt < t1 (since job_arrival jlp < t1 and job_arrival jlp ≤ pt → we need pt < t1)
  -- Actually we need to show pt < t1
  have h_pt_lt_t1 : pt < t1 := by
    by_contra h_neg; push_neg at h_neg
    -- pt ≥ t1 → apply not_quiet at pt
    have h_pt_lt_t2 : pt < t2 := lt_of_le_of_lt h_pt_le_t' h_lt
    obtain ⟨jhp, _, h_hep_jhp, h_sched_jhp⟩ :=
      not_quiet_implies_exists_scheduled_hp_job_at_preemption_point
        arr_seq H_arrival_times_are_consistent sched H_jobs_come_from_arrival_sequence
        H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
        H_priority_is_reflexive H_priority_is_transitive
        H_valid_model_with_bounded_nonpreemptive_segments H_work_conserving H_respects_policy
        j H_j_arrives H_job_cost_positive t1 t2 H_busy_interval_prefix
        pt ⟨h_neg, h_pt_lt_t2⟩ h_pt_preempt
    have h_jlp_at_pt := h_cont pt (le_refl _) h_pt_le_t'
    have h_eq := ideal_proc_model_is_a_uniprocessor_model jlp jhp sched pt h_jlp_at_pt h_sched_jhp
    rw [h_eq] at h_lp; exact h_lp h_hep_jhp
  -- t1 > 0 (since job_arrival jlp ≥ 0 and job_arrival jlp < t1)
  have h_t1_pos : 0 < t1 := lt_of_le_of_lt (Nat.zero_le _) h_arr_lt
  -- jlp scheduled at t1 - 1 (since pt ≤ t1-1 ≤ t' and continuous)
  refine ⟨t1 - 1, Nat.sub_lt h_t1_pos Nat.zero_lt_one, ?_⟩
  have h1 : pt ≤ t1 - 1 := Nat.le_pred_of_lt h_pt_lt_t1
  have h2 : t1 - 1 ≤ t' := le_trans (Nat.sub_le t1 1) h_ge
  exact h_cont (t1 - 1) h1 h2

section CaseAnalysis

section Case1

variable (H_is_idle : is_idle sched t1)

include H_is_idle

theorem preemption_time_exists_case1 :
    exists pr_t,
      preemption_time sched pr_t = true /\
      t1 <= pr_t /\ pr_t <= t1 + max_length_of_priority_inversion arr_seq j t1 := by
  refine ⟨t1, ?_, le_refl _, Nat.le_add_right _ _⟩
  have h_none : sched t1 = none := H_is_idle
  simp [preemption_time, h_none]

end Case1

section Case2

variable (jhp : Job)
variable (H_jhp_is_scheduled : scheduled_at sched jhp t1 = true)
variable (H_jhp_hep_priority : hep_job jhp j = true)

include H_jhp_is_scheduled H_jhp_hep_priority H_busy_interval_prefix

theorem preemption_time_exists_case2 :
    exists pr_t,
      preemption_time sched pr_t = true /\
      t1 <= pr_t /\ pr_t <= t1 + max_length_of_priority_inversion arr_seq j t1 := by
  refine ⟨t1, ?_, le_refl _, Nat.le_add_right _ _⟩
  -- jhp is scheduled at t1 with hep priority
  -- Step 1: jhp arrives in arr_seq
  have h_arr_jhp : arrives_in arr_seq jhp :=
    H_jobs_come_from_arrival_sequence jhp t1 H_jhp_is_scheduled
  -- Step 2: jhp has arrived at t1 (jobs_must_arrive_to_execute)
  have h_has_arrived : has_arrived jhp t1 :=
    H_jobs_must_arrive_to_execute jhp t1 H_jhp_is_scheduled
  -- Step 3: jhp is not completed at t1 (completed_jobs_dont_execute)
  have h_not_compl : ¬ completed_by sched jhp t1 := by
    intro h_compl
    have h_serv_lt := H_completed_jobs_dont_execute jhp t1 H_jhp_is_scheduled
    unfold completed_by at h_compl; unfold work at *; omega
  -- Step 4: jhp did NOT arrive before t1 (from quiet_time)
  have h_not_before : ¬ arrived_before jhp t1 := by
    intro h_before
    exact h_not_compl (H_busy_interval_prefix.2.1 jhp h_arr_jhp H_jhp_hep_priority h_before)
  -- Step 5: job_arrival jhp = t1
  have h_arr_eq : job_arrival jhp = t1 := by
    unfold has_arrived at h_has_arrived
    unfold arrived_before at h_not_before
    simp only [instant, duration] at *; omega
  -- Step 6: service sched jhp t1 = 0
  have h_serv_zero : service sched jhp t1 = 0 :=
    Prosa.Analysis.Facts.Behavior.Service.no_service_before_arrival
      sched jhp H_jobs_must_arrive_to_execute t1
      (by rw [h_arr_eq])
  -- Step 7: preemption_time sched t1 = job_preemptable jhp 0 = true
  have h_sched_eq : sched t1 = some jhp := by
    rw [Prosa.Analysis.Facts.Model.Ideal_schedule.scheduled_at_def] at H_jhp_is_scheduled
    exact of_decide_eq_true H_jhp_is_scheduled
  have h_preemptable_zero : job_preemptable jhp 0 = true :=
    (H_valid_model_with_bounded_nonpreemptive_segments.1 jhp h_arr_jhp).1
  simp [preemption_time, h_sched_eq, h_serv_zero, h_preemptable_zero]

end Case2

section Case3

variable (jlp : Job)
variable (H_jlp_is_scheduled : scheduled_at sched jlp t1 = true)
variable (H_jlp_low_priority : ¬(hep_job jlp j = true))

include H_jlp_is_scheduled H_jlp_low_priority

section FirstPreemptionPointOfjlp

variable (fpt : instant)
variable (H_fpt_is_preemption_point : job_preemptable jlp (service sched jlp t1 + fpt) = true)
variable (H_fpt_is_first_preemption_point :
    ∀ ρ,
      service sched jlp t1 ≤ ρ ∧ ρ ≤ service sched jlp t1 + (job_max_nonpreemptive_segment jlp - ε) →
      job_preemptable jlp ρ = true →
      service sched jlp t1 + fpt ≤ ρ)
variable (H_progr_le_max_nonp_segment :
    service sched jlp t1 ≤ service sched jlp t1 + fpt ∧
    service sched jlp t1 + fpt ≤ service sched jlp t1 + (job_max_nonpreemptive_segment jlp - ε))

include H_fpt_is_preemption_point H_fpt_is_first_preemption_point H_progr_le_max_nonp_segment

theorem no_intermediate_preemption_point :
    ∀ ρ,
      service sched jlp t1 ≤ ρ ∧ ρ < service sched jlp t1 + fpt →
      ¬(job_preemptable jlp ρ = true) := by
  intro ρ ⟨h_le, h_lt⟩ h_preemptable
  have h_bound : ρ ≤ service sched jlp t1 + (job_max_nonpreemptive_segment jlp - ε) :=
    le_of_lt (lt_of_lt_of_le h_lt H_progr_le_max_nonp_segment.2)
  have h_min := H_fpt_is_first_preemption_point ρ ⟨h_le, h_bound⟩ h_preemptable
  exact absurd h_lt (Nat.not_lt.mpr h_min)

theorem continuously_scheduled_between_preemption_points :
    ∀ t',
      t1 ≤ t' ∧ t' < t1 + fpt →
      scheduled_at sched jlp t' = true := by
  intro t' ⟨h_ge, h_lt⟩
  have h_arr_jlp := H_jobs_come_from_arrival_sequence jlp t1 H_jlp_is_scheduled
  have ⟨_, _, h_nps, _⟩ := H_valid_model_with_bounded_nonpreemptive_segments.1 jlp h_arr_jlp
  have h_mono : service sched jlp t1 ≤ service sched jlp t' :=
    Prosa.Analysis.Facts.Behavior.Service.service_monotonic sched jlp t1 t' h_ge
  have h_upper : service sched jlp t' < service sched jlp t1 + fpt := by
    have key : service_during sched jlp t1 t' ≤ t' - t1 := by
      have := Prosa.Analysis.Facts.Behavior.Service.cumulative_service_le_delta
        ideal_proc_model_provides_unit_service sched jlp t1 (t' - t1)
      rwa [Nat.add_sub_cancel' h_ge] at this
    have h_cat := Prosa.Analysis.Facts.Behavior.Service.service_cat sched jlp t1 t' h_ge
    rw [← h_cat]
    exact Nat.add_lt_add_left
      (Nat.lt_of_le_of_lt key (by
        have : t1 + (t' - t1) < t1 + fpt := by rw [Nat.add_sub_cancel' h_ge]; exact h_lt
        exact Nat.lt_of_add_lt_add_left this)) _
  have h_npp : ¬(job_preemptable jlp (service sched jlp t') = true) := by
    intro h_preemptable
    have h_bound : service sched jlp t' ≤ service sched jlp t1 + (job_max_nonpreemptive_segment jlp - ε) :=
      le_of_lt (lt_of_lt_of_le h_upper H_progr_le_max_nonp_segment.2)
    have h_min := H_fpt_is_first_preemption_point (service sched jlp t')
      ⟨h_mono, h_bound⟩ h_preemptable
    exact absurd h_upper (Nat.not_lt.mpr h_min)
  exact h_nps t' h_npp

theorem first_preemption_time :
    preemption_time sched (t1 + fpt) = true := by
  unfold preemption_time
  split
  · next j' h_sched_eq =>
    -- sched (t1 + fpt) = some j', need: job_preemptable j' (service sched j' (t1 + fpt)) = true
    by_cases h_eq : jlp = j'
    · -- Case: j' = jlp
      subst h_eq
      -- Show service(jlp, t1+fpt) = service(jlp, t1) + fpt, then use H_fpt_is_preemption_point
      have h_sd_eq : service_during sched jlp t1 (t1 + fpt) = fpt := by
        simp only [service_during]
        have h_eq_summands : ∀ i ∈ Finset.Ico t1 (t1 + fpt), service_at sched jlp i = 1 := by
          intro i hi; rw [Finset.mem_Ico] at hi
          rw [service_at_is_scheduled_at]
          have h_arr_jlp := H_jobs_come_from_arrival_sequence jlp t1 H_jlp_is_scheduled
          have ⟨_, _, h_nps, _⟩ := H_valid_model_with_bounded_nonpreemptive_segments.1 jlp h_arr_jlp
          have h_mono : service sched jlp t1 ≤ service sched jlp i :=
            Prosa.Analysis.Facts.Behavior.Service.service_monotonic sched jlp t1 i hi.1
          have h_upper : service sched jlp i < service sched jlp t1 + fpt := by
            have h_sd_le := Prosa.Analysis.Facts.Behavior.Service.cumulative_service_le_delta
              ideal_proc_model_provides_unit_service sched jlp t1 (i - t1)
            rw [Nat.add_sub_cancel' hi.1] at h_sd_le
            have h_cat_i := Prosa.Analysis.Facts.Behavior.Service.service_cat sched jlp t1 i hi.1
            calc service sched jlp i
                = service sched jlp t1 + service_during sched jlp t1 i := h_cat_i.symm
              _ ≤ service sched jlp t1 + (i - t1) := Nat.add_le_add_left h_sd_le _
              _ < service sched jlp t1 + fpt := by
                    apply Nat.add_lt_add_left
                    exact Nat.lt_of_add_lt_add_left (by rw [Nat.add_sub_cancel' hi.1]; exact hi.2)
          have h_npp : ¬(job_preemptable jlp (service sched jlp i) = true) := by
            intro h_preemptable
            have h_bound : service sched jlp i ≤ service sched jlp t1 + (job_max_nonpreemptive_segment jlp - ε) :=
              le_of_lt (lt_of_lt_of_le h_upper H_progr_le_max_nonp_segment.2)
            have h_min := H_fpt_is_first_preemption_point (service sched jlp i)
              ⟨h_mono, h_bound⟩ h_preemptable
            exact absurd h_upper (Nat.not_lt.mpr h_min)
          have h_sched_i := h_nps i h_npp
          rw [h_sched_i]; rfl
        rw [Finset.sum_congr rfl h_eq_summands]
        exact Prosa.Util.Sum.sum_of_ones t1 fpt
      have h_cat := Prosa.Analysis.Facts.Behavior.Service.service_cat
        sched jlp t1 (t1 + fpt) (Nat.le_add_right _ _)
      -- h_cat : service t1 + service_during t1 (t1+fpt) = service (t1+fpt)
      -- h_sd_eq : service_during t1 (t1+fpt) = fpt
      -- goal : job_preemptable jlp (service sched jlp (t1 + fpt)) = true
      have h_serv : service sched jlp (t1 + fpt) = service sched jlp t1 + fpt := by
        have := h_cat; rw [h_sd_eq] at this; exact this.symm
      rw [h_serv]; exact H_fpt_is_preemption_point
    · -- Case: j' ≠ jlp
      have h_ne : jlp ≠ j' := h_eq
      cases h_fpt_cases : fpt with
      | zero =>
        exfalso
        have h_jlp := H_jlp_is_scheduled
        rw [scheduled_at_def] at h_jlp
        have h_jlp_eq := of_decide_eq_true h_jlp
        simp only [h_fpt_cases, Nat.add_zero] at h_sched_eq
        rw [h_sched_eq] at h_jlp_eq
        exact h_ne (Option.some_injective _ h_jlp_eq.symm)
      | succ sm =>
        have h_arr_j' := H_jobs_come_from_arrival_sequence j' (t1 + fpt) (by
          rw [scheduled_at_def]; exact decide_eq_true h_sched_eq)
        have ⟨_, _, _, h_esp⟩ := H_valid_model_with_bounded_nonpreemptive_segments.1 j' h_arr_j'
        -- execution_starts_with_preemption_point: j' not at t1+sm, j' at t1+sm+1
        have h_fpt_eq : fpt = sm + 1 := h_fpt_cases
        change job_preemptable j' (service sched j' ((t1 + sm) + 1)) = true
        apply h_esp (t1 + sm)
        · -- j' not scheduled at t1 + sm
          intro h_sched_sm
          have h_arr_jlp := H_jobs_come_from_arrival_sequence jlp t1 H_jlp_is_scheduled
          have ⟨_, _, h_nps_jlp, _⟩ := H_valid_model_with_bounded_nonpreemptive_segments.1 jlp h_arr_jlp
          have h_mono : service sched jlp t1 ≤ service sched jlp (t1 + sm) :=
            Prosa.Analysis.Facts.Behavior.Service.service_monotonic sched jlp t1 (t1 + sm) (Nat.le_add_right _ _)
          have h_upper_sm : service sched jlp (t1 + sm) < service sched jlp t1 + fpt := by
            have h_sd_le := Prosa.Analysis.Facts.Behavior.Service.cumulative_service_le_delta
              ideal_proc_model_provides_unit_service sched jlp t1 sm
            have h_cat_sm := Prosa.Analysis.Facts.Behavior.Service.service_cat
              sched jlp t1 (t1 + sm) (Nat.le_add_right _ _)
            calc service sched jlp (t1 + sm)
                = service sched jlp t1 + service_during sched jlp t1 (t1 + sm) := h_cat_sm.symm
              _ ≤ service sched jlp t1 + sm := Nat.add_le_add_left h_sd_le _
              _ < service sched jlp t1 + fpt := by
                    apply Nat.add_lt_add_left; rw [h_fpt_eq]; exact Nat.lt_succ_of_le (Nat.le_refl _)
          have h_npp_sm : ¬(job_preemptable jlp (service sched jlp (t1 + sm)) = true) := by
            intro h_preemptable
            have h_bound : service sched jlp (t1 + sm) ≤ service sched jlp t1 + (job_max_nonpreemptive_segment jlp - ε) :=
              le_of_lt (lt_of_lt_of_le h_upper_sm H_progr_le_max_nonp_segment.2)
            have h_min := H_fpt_is_first_preemption_point (service sched jlp (t1 + sm))
              ⟨h_mono, h_bound⟩ h_preemptable
            exact absurd h_upper_sm (Nat.not_lt.mpr h_min)
          have h_jlp_at_sm := h_nps_jlp (t1 + sm) h_npp_sm
          have h_uni := ideal_proc_model_is_a_uniprocessor_model jlp j'
            sched (t1 + sm) h_jlp_at_sm h_sched_sm
          exact h_ne h_uni
        · -- j' scheduled at t1 + sm + 1
          rw [scheduled_at_def]
          rw [h_fpt_cases] at h_sched_eq
          exact decide_eq_true h_sched_eq
  · rfl

include H_j_arrives H_job_cost_positive H_busy_interval_prefix in
theorem preemption_time_le_max_len_of_priority_inversion :
    t1 ≤ t1 + fpt ∧ t1 + fpt ≤ t1 + max_length_of_priority_inversion arr_seq j t1 := by
  constructor
  · exact Nat.le_add_right _ _
  · apply Nat.add_le_add_left
    -- fpt ≤ max_length_of_priority_inversion arr_seq j t1
    have h_fpt_le : fpt ≤ job_max_nonpreemptive_segment jlp - ε :=
      Nat.le_of_add_le_add_left H_progr_le_max_nonp_segment.2
    have h_arr_jlp := H_jobs_come_from_arrival_sequence jlp t1 H_jlp_is_scheduled
    have h_arrive_lt := low_priority_job_arrives_before_busy_interval_prefix
      arr_seq H_arrival_times_are_consistent sched H_jobs_come_from_arrival_sequence
      H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
      H_priority_is_reflexive H_priority_is_transitive
      H_valid_model_with_bounded_nonpreemptive_segments H_work_conserving H_respects_policy
      j H_j_arrives H_job_cost_positive t1 t2 H_busy_interval_prefix
      jlp t1 ⟨le_refl _, H_busy_interval_prefix.1⟩ H_jlp_is_scheduled H_jlp_low_priority
    have h_ab : arrived_between jlp 0 t1 := ⟨Nat.zero_le _, h_arrive_lt⟩
    have h_mem : jlp ∈ arrivals_before arr_seq t1 := by
      show jlp ∈ arrivals_between arr_seq 0 t1
      exact Prosa.Analysis.Facts.Behavior.Arrivals.arrived_between_implies_in_arrivals
        arr_seq H_arrival_times_are_consistent jlp 0 t1 h_arr_jlp h_ab
    unfold max_length_of_priority_inversion
    exact le_trans h_fpt_le
      (leq_bigmax_cond_seq (fun j_lp => ¬(hep_job j_lp j = true))
        (arrivals_before arr_seq t1)
        (fun j_lp => job_max_nonpreemptive_segment j_lp - ε)
        jlp h_mem H_jlp_low_priority)

end FirstPreemptionPointOfjlp

include H_j_arrives H_job_cost_positive H_busy_interval_prefix in
theorem preemption_time_exists_case3 :
    exists pr_t,
      preemption_time sched pr_t = true /\
      t1 <= pr_t /\ pr_t <= t1 + max_length_of_priority_inversion arr_seq j t1 := by
  -- Get the bounded nonpreemptive segments property for jlp
  have h_arr_jlp := H_jobs_come_from_arrival_sequence jlp t1 H_jlp_is_scheduled
  have ⟨_, h_nrbl⟩ := H_valid_model_with_bounded_nonpreemptive_segments.2 jlp h_arr_jlp
  -- Get a preemptable point in the range [service jlp t1, service jlp t1 + (jmns - ε)]
  have h_serv_le_cost : service sched jlp t1 ≤ job_cost jlp :=
    le_of_lt (H_completed_jobs_dont_execute jlp t1 H_jlp_is_scheduled)
  obtain ⟨pp, h_pp_ge, h_pp_le, h_pp_preempt⟩ :=
    h_nrbl (service sched jlp t1) ⟨Nat.zero_le _, h_serv_le_cost⟩
  -- Find the MINIMUM such preemptable point using Nat.find
  let P : ℕ → Prop := fun pt =>
    (service sched jlp t1 ≤ pt ∧ pt ≤ service sched jlp t1 + (job_max_nonpreemptive_segment jlp - ε)) ∧
    job_preemptable jlp pt = true
  have h_ex : ∃ n, P n := ⟨pp, ⟨h_pp_ge, h_pp_le⟩, h_pp_preempt⟩
  have h_dec : DecidablePred P := by
    intro n; exact instDecidableAnd
  let sm := Nat.find h_ex
  have h_sm_spec : P sm := Nat.find_spec h_ex
  have h_sm_min : ∀ k, P k → sm ≤ k := by
    intro k hk
    exact Nat.find_min' h_ex hk
  -- sm = service jlp t1 + Δ for some Δ
  have h_sm_ge : service sched jlp t1 ≤ sm := h_sm_spec.1.1
  let Δ := sm - service sched jlp t1
  have h_sm_eq : sm = service sched jlp t1 + Δ := by
    exact (Nat.add_sub_cancel' h_sm_ge).symm
  -- Verify the properties in terms of Δ
  have h_delta_preempt : job_preemptable jlp (service sched jlp t1 + Δ) = true := by
    rw [← h_sm_eq]; exact h_sm_spec.2
  have h_delta_first : ∀ ρ,
      service sched jlp t1 ≤ ρ ∧ ρ ≤ service sched jlp t1 + (job_max_nonpreemptive_segment jlp - ε) →
      job_preemptable jlp ρ = true →
      service sched jlp t1 + Δ ≤ ρ := by
    intro ρ h_range h_p
    rw [← h_sm_eq]
    exact h_sm_min ρ ⟨h_range, h_p⟩
  have h_delta_range :
      service sched jlp t1 ≤ service sched jlp t1 + Δ ∧
      service sched jlp t1 + Δ ≤ service sched jlp t1 + (job_max_nonpreemptive_segment jlp - ε) := by
    rw [← h_sm_eq]
    exact h_sm_spec.1
  -- Apply first_preemption_time and preemption_time_le_max_len
  refine ⟨t1 + Δ, ?_, ?_⟩
  · exact first_preemption_time
      arr_seq H_arrival_times_are_consistent sched H_jobs_come_from_arrival_sequence
      H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
      H_priority_is_reflexive H_priority_is_transitive
      H_valid_model_with_bounded_nonpreemptive_segments H_work_conserving H_respects_policy
      j t1 jlp H_jlp_is_scheduled H_jlp_low_priority
      Δ h_delta_preempt h_delta_first h_delta_range
  · exact preemption_time_le_max_len_of_priority_inversion
      arr_seq H_arrival_times_are_consistent sched H_jobs_come_from_arrival_sequence
      H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
      H_priority_is_reflexive H_priority_is_transitive
      H_valid_model_with_bounded_nonpreemptive_segments H_work_conserving H_respects_policy
      j (by exact H_j_arrives) (by exact H_job_cost_positive)
      t1 t2 (by exact H_busy_interval_prefix)
      jlp H_jlp_is_scheduled H_jlp_low_priority
      Δ h_delta_preempt h_delta_first h_delta_range

end Case3

end CaseAnalysis

include H_j_arrives H_job_cost_positive H_busy_interval_prefix in
theorem preemption_time_exists :
    exists pr_t,
      preemption_time sched pr_t = true /\
      t1 <= pr_t /\ pr_t <= t1 + max_length_of_priority_inversion arr_seq j t1 := by
  rcases h_opt : sched t1 with _ | s
  · -- idle case
    exact preemption_time_exists_case1
      arr_seq H_arrival_times_are_consistent sched H_jobs_come_from_arrival_sequence
      H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
      H_priority_is_reflexive H_priority_is_transitive
      H_valid_model_with_bounded_nonpreemptive_segments H_work_conserving H_respects_policy
      j t1 h_opt
  · -- scheduled case: sched t1 = some s
    have h_sched : scheduled_at sched s t1 = true := by
      rw [scheduled_at_def]; exact decide_eq_true h_opt
    by_cases h_prio : hep_job s j = true
    · -- s has hep priority
      exact preemption_time_exists_case2
        arr_seq H_arrival_times_are_consistent sched H_jobs_come_from_arrival_sequence
        H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
        H_priority_is_reflexive H_priority_is_transitive
        H_valid_model_with_bounded_nonpreemptive_segments H_work_conserving H_respects_policy
        j t1 t2 H_busy_interval_prefix s h_sched h_prio
    · -- s has low priority
      exact preemption_time_exists_case3
        arr_seq H_arrival_times_are_consistent sched H_jobs_come_from_arrival_sequence
        H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
        H_priority_is_reflexive H_priority_is_transitive
        H_valid_model_with_bounded_nonpreemptive_segments H_work_conserving H_respects_policy
        j H_j_arrives H_job_cost_positive t1 t2 H_busy_interval_prefix
        s h_sched h_prio

end PreemptionTimeExists

end PriorityInversionIsBounded

end Prosa.Analysis.Facts.Busy_interval.Priority_inversion
