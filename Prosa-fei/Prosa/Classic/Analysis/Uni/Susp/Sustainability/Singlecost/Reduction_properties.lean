-- Translated from: ../rt-proofs/classic/analysis/uni/susp/sustainability/singlecost/reduction_properties.v
import Prosa.Classic.Util.All
import Prosa.Classic.Model.Priority
import Prosa.Classic.Model.Arrival.Basic.Arrival_sequence
import Prosa.Classic.Model.Schedule.Uni.Response_time
import Prosa.Classic.Model.Schedule.Uni.Susp.Suspension_intervals
import Prosa.Classic.Model.Schedule.Uni.Susp.Schedule
import Prosa.Classic.Model.Schedule.Uni.Susp.Platform
import Prosa.Classic.Analysis.Uni.Susp.Sustainability.Singlecost.Reduction
import Prosa.Classic.Model.Schedule.Uni.Transformation.Construction

namespace Prosa.Classic.Analysis.Uni.Susp.Sustainability.Singlecost.Reduction_properties

open Prosa.Classic.Model.Time
open Prosa.Classic.Model.Schedule.Uni.Susp.Schedule
open Prosa.Classic.Model.Suspension
open Prosa.Classic.Model.Priority
open Prosa.Classic.Model.Schedule.Uni.Susp.Suspension_intervals
open Prosa.Classic.Model.Schedule.Uni.Susp.Platform.PlatformWithSuspensions
open Prosa.Classic.Model.Schedule.Uni.Response_time.ResponseTime
open Prosa.Classic.Model.Schedule.Uni.Transformation.Construction.ScheduleConstruction
open Prosa.Classic.Model.Schedule.Uni.Schedule
open Prosa.Classic.Model.Arrival.Basic.Arrival_sequence
open Prosa.Classic.Model.Schedule.Uni.Susp.Last_execution
open Prosa.Classic.Util.Minmax
open Prosa.Classic.Analysis.Uni.Susp.Sustainability.Singlecost.Reduction.SustainabilitySingleCost
open Classical

noncomputable section

namespace SustainabilitySingleCostProperties

section ReductionProperties

variable {Job : Type _} [DecidableEq Job]
variable (job_arrival : Job → Time)
variable (job_cost : Job → Time)

variable (arr_seq : arrival_sequence Job)
variable (H_arrival_times_are_consistent :
  arrival_times_are_consistent job_arrival arr_seq)

variable (higher_eq_priority : JLDP_policy Job)
variable (H_priority_is_reflexive : JLDP_is_reflexive higher_eq_priority)
variable (H_priority_is_transitive : JLDP_is_transitive higher_eq_priority)
variable (H_priority_is_total : JLDP_is_total arr_seq higher_eq_priority)

variable (sched_susp : schedule Job)
variable (H_jobs_come_from_arrival_sequence :
  jobs_come_from_arrival_sequence sched_susp arr_seq)

variable (job_suspension_duration : job_suspension Job)

variable (H_jobs_must_arrive_to_execute :
  jobs_must_arrive_to_execute job_arrival sched_susp)

variable (H_completed_jobs_dont_execute :
  completed_jobs_dont_execute job_cost sched_susp)

variable (H_work_conserving :
  work_conserving job_arrival job_cost job_suspension_duration arr_seq sched_susp)

variable (H_respects_priority :
  respects_JLDP_policy job_arrival job_cost job_suspension_duration arr_seq
    sched_susp higher_eq_priority)

variable (H_respects_self_suspensions :
  respects_self_suspensions job_arrival job_cost job_suspension_duration sched_susp)

variable (j : Job)

variable (inflated_job_cost : Job → Time)

variable (H_cost_of_j_does_not_decrease : inflated_job_cost j ≥ job_cost j)

variable (H_inflation_only_for_job_j :
  ∀ any_j, any_j ≠ j → inflated_job_cost any_j = job_cost any_j)

section PropertiesOfScheduleConstruction

include H_arrival_times_are_consistent H_priority_is_reflexive H_priority_is_transitive H_priority_is_total H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_work_conserving H_respects_priority H_respects_self_suspensions H_cost_of_j_does_not_decrease H_inflation_only_for_job_j in
theorem sched_susp_highercost_depends_only_on_prefix :
    ∀ sched1 sched2 t,
      (∀ t0, t0 < t → sched1 t0 = sched2 t0) →
      build_schedule job_arrival arr_seq higher_eq_priority sched_susp
        job_suspension_duration inflated_job_cost sched1 t =
      build_schedule job_arrival arr_seq higher_eq_priority sched_susp
        job_suspension_duration inflated_job_cost sched2 t := by
  intro sched1 sched2 t ALL
  -- Helper: rewriting schedule values implies equal service_at
  have ALL_sa : ∀ j0 i, i < t → service_at sched1 j0 i = service_at sched2 j0 i := by
    intro j0 i hi; simp only [service_at, scheduled_at]; rw [ALL i hi]
  -- Step 1: Show service is the same for both schedules up to time t
  have SERV : ∀ j0, service sched1 j0 t = service sched2 j0 t := by
    intro j0; simp only [service, service_during]
    apply Finset.sum_congr rfl
    intro i hi; rw [Finset.mem_Ico] at hi
    exact ALL_sa j0 i hi.2
  -- Helper: service is the same for any time up to the last execution (which is ≤ t)
  have SERV_le : ∀ j0 t', t' ≤ t → service sched1 j0 t' = service sched2 j0 t' := by
    intro j0 t' ht'; simp only [service, service_during]
    apply Finset.sum_congr rfl
    intro i hi; rw [Finset.mem_Ico] at hi
    exact ALL_sa j0 i (Nat.lt_of_lt_of_le hi.2 ht')
  -- Step 2: Show completed_by is the same
  have COMP : ∀ j0, completed_by inflated_job_cost sched1 j0 t ↔ completed_by inflated_job_cost sched2 j0 t := by
    intro j0; simp only [completed_by]; rw [SERV j0]
  -- Step 3: Show pending is the same
  have PEND : ∀ j0, pending job_arrival inflated_job_cost sched1 j0 t ↔ pending job_arrival inflated_job_cost sched2 j0 t := by
    intro j0; simp only [pending]
    constructor
    · intro ⟨harr, hnc⟩; exact ⟨harr, fun hc => hnc ((COMP j0).mpr hc)⟩
    · intro ⟨harr, hnc⟩; exact ⟨harr, fun hc => hnc ((COMP j0).mp hc)⟩
  -- Step 4: Show scheduled_before is the same
  have EX : ∀ j0, (∃ t0 : Fin t, scheduled_at sched1 j0 t0.val = true) ↔
                   (∃ t0 : Fin t, scheduled_at sched2 j0 t0.val = true) := by
    intro j0
    constructor
    · rintro ⟨⟨t0, ht0⟩, hsched⟩
      exact ⟨⟨t0, ht0⟩, by simp only [scheduled_at] at hsched ⊢; rw [← ALL t0 ht0]; exact hsched⟩
    · rintro ⟨⟨t0, ht0⟩, hsched⟩
      exact ⟨⟨t0, ht0⟩, by simp only [scheduled_at] at hsched ⊢; rw [ALL t0 ht0]; exact hsched⟩
  -- Step 5: Show time_after_last_execution is the same
  have BEG : ∀ j0, time_after_last_execution job_arrival sched1 j0 t =
                    time_after_last_execution job_arrival sched2 j0 t := by
    intro j0
    simp only [time_after_last_execution, scheduled_before, last_time_scheduled]
    have h_sb_eq : decide (∃ t0 : Fin t, scheduled_at sched1 j0 t0.val = true) =
                   decide (∃ t0 : Fin t, scheduled_at sched2 j0 t0.val = true) := by
      congr 1; exact propext (EX j0)
    rw [h_sb_eq]
    split
    · rename_i h_sb
      have h_same_mnc : max_nat_cond (fun t0 => scheduled_at sched1 j0 t0) 0 t =
                        max_nat_cond (fun t0 => scheduled_at sched2 j0 t0) 0 t := by
        simp only [max_nat_cond]; congr 1
        apply List.filter_congr
        intro i hi
        have hv := (mem_values_between 0 t i).mp hi
        simp only [scheduled_at]; rw [ALL i hv.2]
      rw [h_same_mnc]
    · rfl
  -- Helper: time_after_last_execution is bounded by t for any schedule when has_arrived
  have tae_le : ∀ (s : schedule Job) j0, has_arrived job_arrival j0 t →
      time_after_last_execution job_arrival s j0 t ≤ t := by
    intro s j0 harr
    simp only [time_after_last_execution]
    split
    · rename_i h_sb
      simp only [scheduled_before, decide_eq_true_eq] at h_sb
      obtain ⟨⟨t0, ht0⟩, hsched⟩ := h_sb
      simp only [last_time_scheduled]
      have hne : max_nat_cond (fun t0 => scheduled_at s j0 t0) 0 t ≠ none :=
        max_nat_cond_exists _ _ _ t0 ⟨Nat.zero_le _, ht0⟩ hsched
      obtain ⟨m, hm⟩ : ∃ m, max_nat_cond (fun t0 => scheduled_at s j0 t0) 0 t = some m := by
        cases h : max_nat_cond (fun t0 => scheduled_at s j0 t0) 0 t with
        | some m => exact ⟨m, rfl⟩ | none => exact absurd h hne
      rw [hm]
      have hinfo := max_nat_cond_in_seq _ _ _ _ hm
      exact Nat.succ_le_of_lt hinfo.2.1
    · exact harr
  -- Step 6: Show suspension_duration is the same for arrived jobs
  have SUSP : ∀ j0, has_arrived job_arrival j0 t →
      suspension_duration job_arrival job_suspension_duration sched1 j0 t =
      suspension_duration job_arrival job_suspension_duration sched2 j0 t := by
    intro j0 harr
    simp only [suspension_duration]; rw [BEG j0]; congr 1
    exact SERV_le j0 _ (tae_le sched2 j0 harr)
  -- Step 7: Show suspended_at is the same for arrived jobs
  have SUSPat : ∀ j0, has_arrived job_arrival j0 t →
      (suspended_at job_arrival inflated_job_cost job_suspension_duration sched1 j0 t ↔
       suspended_at job_arrival inflated_job_cost job_suspension_duration sched2 j0 t) := by
    intro j0 harr
    simp only [suspended_at, suspension_duration]; rw [BEG j0]
    have hserv_eq := SERV_le j0 _ (tae_le sched2 j0 harr)
    rw [hserv_eq]
    exact ⟨fun ⟨hnc, h⟩ => ⟨fun hc => hnc ((COMP j0).mpr hc), h⟩,
           fun ⟨hnc, h⟩ => ⟨fun hc => hnc ((COMP j0).mp hc), h⟩⟩
  -- Step 8: Show ready_jobs is the same
  have SAMEready : ready_jobs job_arrival arr_seq job_suspension_duration inflated_job_cost sched1 t =
                   ready_jobs job_arrival arr_seq job_suspension_duration inflated_job_cost sched2 t := by
    simp only [ready_jobs]
    apply List.filter_congr
    intro j0 hin
    have harr : has_arrived job_arrival j0 t := by
      have hb := in_arrivals_implies_arrived_between job_arrival arr_seq H_arrival_times_are_consistent j0 0 (t + 1) hin
      unfold arrived_between has_arrived at *; simp only [Time] at *; omega
    have h1 : decide (pending job_arrival inflated_job_cost sched1 j0 t) =
              decide (pending job_arrival inflated_job_cost sched2 j0 t) := by
      congr 1; exact propext (PEND j0)
    have h2 : decide (suspended_at job_arrival inflated_job_cost job_suspension_duration sched1 j0 t) =
              decide (suspended_at job_arrival inflated_job_cost job_suspension_duration sched2 j0 t) := by
      congr 1; exact propext (SUSPat j0 harr)
    rw [h1, h2]
  -- Step 9: Conclude build_schedule is the same
  -- We need: build_schedule ... sched1 t = build_schedule ... sched2 t
  -- build_schedule unfolds to matching on highest_priority_job, then sched_susp t, then if-condition
  -- After SAMEready, the hp_job and ready_jobs are the same
  -- The only difference is the if-condition in the some/some case
  unfold build_schedule
  rw [show highest_priority_job job_arrival arr_seq higher_eq_priority job_suspension_duration inflated_job_cost sched1 t =
      highest_priority_job job_arrival arr_seq higher_eq_priority job_suspension_duration inflated_job_cost sched2 t from by
    unfold highest_priority_job; rw [SAMEready]]
  cases highest_priority_job job_arrival arr_seq higher_eq_priority job_suspension_duration
    inflated_job_cost sched2 t with
  | none => rfl
  | some j_hp =>
    cases h_susp : sched_susp t with
    | none => rfl
    | some j_in_susp =>
      -- Need to show the if-condition is the same
      have harr_susp : has_arrived job_arrival j_in_susp t := by
        apply H_jobs_must_arrive_to_execute
        show scheduled_at sched_susp j_in_susp t = true
        simp only [scheduled_at]; rw [h_susp]; simp
      simp only
      rw [show decide (pending job_arrival inflated_job_cost sched1 j_in_susp t) =
              decide (pending job_arrival inflated_job_cost sched2 j_in_susp t) from
            by congr 1; exact propext (PEND j_in_susp),
          show decide (suspended_at job_arrival inflated_job_cost job_suspension_duration sched1 j_in_susp t) =
              decide (suspended_at job_arrival inflated_job_cost job_suspension_duration sched2 j_in_susp t) from
            by congr 1; exact propext (SUSPat j_in_susp harr_susp)]

include H_arrival_times_are_consistent H_priority_is_reflexive H_priority_is_transitive H_priority_is_total H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_work_conserving H_respects_priority H_respects_self_suspensions H_cost_of_j_does_not_decrease H_inflation_only_for_job_j in
theorem sched_susp_highercost_uses_construction_function :
    ∀ t,
      sched_susp_highercost job_arrival arr_seq higher_eq_priority sched_susp
        job_suspension_duration inflated_job_cost t =
      build_schedule job_arrival arr_seq higher_eq_priority sched_susp
        job_suspension_duration inflated_job_cost
        (sched_susp_highercost job_arrival arr_seq higher_eq_priority sched_susp
          job_suspension_duration inflated_job_cost) t := by
  intro t
  exact prefix_dependent_schedule_construction
    (build_schedule job_arrival arr_seq higher_eq_priority sched_susp
      job_suspension_duration inflated_job_cost)
    (fun _ => none)
    (sched_susp_highercost_depends_only_on_prefix job_arrival job_cost arr_seq
      H_arrival_times_are_consistent higher_eq_priority H_priority_is_reflexive
      H_priority_is_transitive H_priority_is_total sched_susp
      H_jobs_come_from_arrival_sequence job_suspension_duration
      H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
      H_work_conserving H_respects_priority H_respects_self_suspensions j
      inflated_job_cost H_cost_of_j_does_not_decrease H_inflation_only_for_job_j)
    t

end PropertiesOfScheduleConstruction

section ScheduleIsValid

include H_arrival_times_are_consistent H_priority_is_reflexive H_priority_is_transitive H_priority_is_total H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_work_conserving H_respects_priority H_respects_self_suspensions H_cost_of_j_does_not_decrease H_inflation_only_for_job_j in
theorem sched_susp_highercost_jobs_come_from_arrival_sequence :
    jobs_come_from_arrival_sequence
      (sched_susp_highercost job_arrival arr_seq higher_eq_priority sched_susp
        job_suspension_duration inflated_job_cost) arr_seq := by
  intro j0 t SCHED
  -- Get the actual schedule value
  have SCHED_eq : sched_susp_highercost job_arrival arr_seq higher_eq_priority sched_susp
      job_suspension_duration inflated_job_cost t = some j0 := by
    simp only [scheduled_at] at SCHED; rwa [beq_iff_eq] at SCHED
  -- Rewrite using construction function
  rw [sched_susp_highercost_uses_construction_function job_arrival job_cost arr_seq
    H_arrival_times_are_consistent higher_eq_priority H_priority_is_reflexive
    H_priority_is_transitive H_priority_is_total sched_susp
    H_jobs_come_from_arrival_sequence job_suspension_duration
    H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
    H_work_conserving H_respects_priority H_respects_self_suspensions j
    inflated_job_cost H_cost_of_j_does_not_decrease H_inflation_only_for_job_j t] at SCHED_eq
  -- Unfold build_schedule
  simp only [build_schedule] at SCHED_eq
  set hp := highest_priority_job job_arrival arr_seq higher_eq_priority job_suspension_duration
    inflated_job_cost
    (sched_susp_highercost job_arrival arr_seq higher_eq_priority sched_susp
      job_suspension_duration inflated_job_cost) t with hp_def
  cases h_hp : hp with
  | none => simp [h_hp] at SCHED_eq
  | some j_hp =>
    -- j_hp ∈ ready_jobs
    have IN : j_hp ∈ ready_jobs job_arrival arr_seq job_suspension_duration inflated_job_cost
        (sched_susp_highercost job_arrival arr_seq higher_eq_priority sched_susp
          job_suspension_duration inflated_job_cost) t := by
      exact seq_min_in_seq _ _ _ h_hp
    -- j_hp arrives_in arr_seq
    have ARRhp : arrives_in arr_seq j_hp := by
      simp only [ready_jobs, List.mem_filter] at IN
      exact in_arrivals_implies_arrived job_arrival arr_seq H_arrival_times_are_consistent j_hp 0 (t + 1) IN.1
    simp [h_hp] at SCHED_eq
    cases h_susp : sched_susp t with
    | none =>
      simp [h_susp] at SCHED_eq
      subst SCHED_eq; exact ARRhp
    | some j_s =>
      simp [h_susp] at SCHED_eq
      have ARRs : arrives_in arr_seq j_s := by
        apply H_jobs_come_from_arrival_sequence j_s t
        simp only [scheduled_at]; rw [h_susp]; simp
      split at SCHED_eq
      · injection SCHED_eq with h; subst h; exact ARRs
      · injection SCHED_eq with h; subst h; exact ARRhp

include H_arrival_times_are_consistent H_priority_is_reflexive H_priority_is_transitive H_priority_is_total H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_work_conserving H_respects_priority H_respects_self_suspensions H_cost_of_j_does_not_decrease H_inflation_only_for_job_j in
theorem sched_susp_highercost_jobs_must_arrive_to_execute :
    jobs_must_arrive_to_execute job_arrival
      (sched_susp_highercost job_arrival arr_seq higher_eq_priority sched_susp
        job_suspension_duration inflated_job_cost) := by
  intro j0 t SCHED
  -- Get the actual schedule value
  have SCHED_eq : sched_susp_highercost job_arrival arr_seq higher_eq_priority sched_susp
      job_suspension_duration inflated_job_cost t = some j0 := by
    simp only [scheduled_at] at SCHED; rwa [beq_iff_eq] at SCHED
  -- Rewrite using construction function
  rw [sched_susp_highercost_uses_construction_function job_arrival job_cost arr_seq
    H_arrival_times_are_consistent higher_eq_priority H_priority_is_reflexive
    H_priority_is_transitive H_priority_is_total sched_susp
    H_jobs_come_from_arrival_sequence job_suspension_duration
    H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
    H_work_conserving H_respects_priority H_respects_self_suspensions j
    inflated_job_cost H_cost_of_j_does_not_decrease H_inflation_only_for_job_j t] at SCHED_eq
  -- Unfold build_schedule
  simp only [build_schedule] at SCHED_eq
  set hp := highest_priority_job job_arrival arr_seq higher_eq_priority job_suspension_duration
    inflated_job_cost
    (sched_susp_highercost job_arrival arr_seq higher_eq_priority sched_susp
      job_suspension_duration inflated_job_cost) t with hp_def
  cases h_hp : hp with
  | none => simp [h_hp] at SCHED_eq
  | some j_hp =>
    -- j_hp ∈ ready_jobs
    have IN : j_hp ∈ ready_jobs job_arrival arr_seq job_suspension_duration inflated_job_cost
        (sched_susp_highercost job_arrival arr_seq higher_eq_priority sched_susp
          job_suspension_duration inflated_job_cost) t := by
      exact seq_min_in_seq _ _ _ h_hp
    -- j_hp has_arrived
    have ARRhp : has_arrived job_arrival j_hp t := by
      simp only [ready_jobs, List.mem_filter] at IN
      have hb := in_arrivals_implies_arrived_between job_arrival arr_seq H_arrival_times_are_consistent j_hp 0 (t + 1) IN.1
      unfold arrived_between has_arrived at *; simp only [Time] at *; omega
    simp [h_hp] at SCHED_eq
    cases h_susp : sched_susp t with
    | none =>
      simp [h_susp] at SCHED_eq
      subst SCHED_eq; exact ARRhp
    | some j_s =>
      simp [h_susp] at SCHED_eq
      have ARRs : has_arrived job_arrival j_s t := by
        apply H_jobs_must_arrive_to_execute
        simp only [scheduled_at]; rw [h_susp]; simp
      split at SCHED_eq
      · injection SCHED_eq with h; subst h; exact ARRs
      · injection SCHED_eq with h; subst h; exact ARRhp

include H_arrival_times_are_consistent H_priority_is_reflexive H_priority_is_transitive H_priority_is_total H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_work_conserving H_respects_priority H_respects_self_suspensions H_cost_of_j_does_not_decrease H_inflation_only_for_job_j in
theorem sched_susp_highercost_completed_jobs_dont_execute :
    completed_jobs_dont_execute inflated_job_cost
      (sched_susp_highercost job_arrival arr_seq higher_eq_priority sched_susp
        job_suspension_duration inflated_job_cost) := by
  set sched_hc := sched_susp_highercost job_arrival arr_seq higher_eq_priority sched_susp
    job_suspension_duration inflated_job_cost with sched_hc_def
  intro j0 t
  induction t with
  | zero =>
    simp only [service, service_during, Finset.Ico_self, Finset.sum_empty]
    exact Nat.zero_le _
  | succ t IHt =>
    -- Case split: IHt is equality or strict
    by_cases hEQ : service sched_hc j0 t = inflated_job_cost j0
    · -- service at t = inflated_job_cost j0, so j0 is completed and shouldn't be scheduled
      -- Need to show service_at j0 t = 0, i.e. j0 is not scheduled at t
      have NOTCOMP : ¬ pending job_arrival inflated_job_cost sched_hc j0 t := by
        intro ⟨_, hnc⟩; exact hnc (show completed_by inflated_job_cost sched_hc j0 t from le_of_eq hEQ.symm)
      -- Show j0 is not scheduled at time t in sched_hc
      have h_not_sched : ¬ (scheduled_at sched_hc j0 t = true) := by
        intro h_sched
        have SCHED_val : sched_hc t = some j0 := by
          simp only [scheduled_at] at h_sched; rwa [beq_iff_eq] at h_sched
        rw [sched_hc_def, sched_susp_highercost_uses_construction_function job_arrival job_cost arr_seq
          H_arrival_times_are_consistent higher_eq_priority H_priority_is_reflexive
          H_priority_is_transitive H_priority_is_total sched_susp
          H_jobs_come_from_arrival_sequence job_suspension_duration
          H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
          H_work_conserving H_respects_priority H_respects_self_suspensions j
          inflated_job_cost H_cost_of_j_does_not_decrease H_inflation_only_for_job_j t] at SCHED_val
        simp only [build_schedule] at SCHED_val
        -- Case on hp_job
        split at SCHED_val
        · -- some j_hp
          rename_i j_hp h_hp_eq
          have IN_hp : j_hp ∈ ready_jobs job_arrival arr_seq job_suspension_duration inflated_job_cost sched_hc t :=
            seq_min_in_seq _ _ _ (sched_hc_def ▸ h_hp_eq)
          have PENDhp : pending job_arrival inflated_job_cost sched_hc j_hp t := by
            simp only [ready_jobs, List.mem_filter, Bool.and_eq_true, decide_eq_true_eq,
              Bool.not_eq_true', decide_eq_false_iff_not] at IN_hp
            exact IN_hp.2.1
          cases h_susp : sched_susp t with
          | none =>
            simp [h_susp] at SCHED_val; subst SCHED_val; exact NOTCOMP PENDhp
          | some j_s =>
            simp [h_susp] at SCHED_val
            split at SCHED_val
            · -- j_s was selected: SCHED_val : some j_s = some j0
              have := Option.some_injective _ SCHED_val; subst this
              rename_i h_cond
              exact NOTCOMP (by rw [← sched_hc_def] at h_cond; exact h_cond.1.1)
            · -- j_hp was selected: SCHED_val : some j_hp = some j0
              have := Option.some_injective _ SCHED_val; subst this
              exact NOTCOMP PENDhp
        · -- none
          simp at SCHED_val
      -- Now we know j0 is not scheduled, so service_at = 0
      have h_sa_zero : service_at sched_hc j0 t = 0 := by
        simp only [service_at, scheduled_at]
        rw [Bool.not_eq_true] at h_not_sched
        simp only [scheduled_at] at h_not_sched
        simp [h_not_sched]
      -- service(t+1) = service(t) + service_at(t) = service(t) + 0 = service(t) = inflated_cost
      have h_split : service sched_hc j0 (t + 1) =
          service sched_hc j0 t + service_at sched_hc j0 t := by
        simp only [service, service_during]
        rw [Finset.sum_Ico_succ_top (Nat.zero_le t)]
      rw [h_split, h_sa_zero, hEQ]; omega
    · -- service at t < inflated_job_cost j0
      have hLT : service sched_hc j0 t < inflated_job_cost j0 := by
        omega
      have h_sa_le := service_at_most_one sched_hc j0 t
      have h_split : service sched_hc j0 (t + 1) =
          service sched_hc j0 t + service_at sched_hc j0 t := by
        simp only [service, service_during]
        rw [Finset.sum_Ico_succ_top (Nat.zero_le t)]
      linarith

include H_arrival_times_are_consistent H_priority_is_reflexive H_priority_is_transitive H_priority_is_total H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_work_conserving H_respects_priority H_respects_self_suspensions H_cost_of_j_does_not_decrease H_inflation_only_for_job_j in
theorem sched_susp_highercost_work_conserving :
    work_conserving job_arrival inflated_job_cost job_suspension_duration arr_seq
      (sched_susp_highercost job_arrival arr_seq higher_eq_priority sched_susp
        job_suspension_duration inflated_job_cost) := by
  set sched_hc := sched_susp_highercost job_arrival arr_seq higher_eq_priority sched_susp
    job_suspension_duration inflated_job_cost with sched_hc_def
  intro j0 t IN BACK
  obtain ⟨PEND, NOTSCHED, NOTSUSP⟩ := BACK
  have SCHED_EQ := sched_susp_highercost_uses_construction_function job_arrival job_cost arr_seq
    H_arrival_times_are_consistent higher_eq_priority H_priority_is_reflexive
    H_priority_is_transitive H_priority_is_total sched_susp
    H_jobs_come_from_arrival_sequence job_suspension_duration
    H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
    H_work_conserving H_respects_priority H_respects_self_suspensions j
    inflated_job_cost H_cost_of_j_does_not_decrease H_inflation_only_for_job_j t
  cases h_hp : highest_priority_job job_arrival arr_seq higher_eq_priority job_suspension_duration
    inflated_job_cost sched_hc t with
  | some j_hp =>
    cases h_susp : sched_susp t with
    | none =>
      exact ⟨j_hp, by
        simp only [scheduled_at]; rw [sched_hc_def, SCHED_EQ, ← sched_hc_def]
        simp only [build_schedule, h_hp, h_susp]; simp [beq_self_eq_true]⟩
    | some j_s =>
      have h_val : sched_hc t = build_schedule job_arrival arr_seq higher_eq_priority sched_susp
          job_suspension_duration inflated_job_cost sched_hc t := by
        rw [sched_hc_def, SCHED_EQ]
      simp only [build_schedule, h_hp, h_susp] at h_val
      split at h_val
      · exact ⟨j_s, by simp only [scheduled_at]; rw [h_val]; simp [beq_self_eq_true]⟩
      · exact ⟨j_hp, by simp only [scheduled_at]; rw [h_val]; simp [beq_self_eq_true]⟩
  | none =>
    exfalso
    have IN0 : j0 ∈ ready_jobs job_arrival arr_seq job_suspension_duration inflated_job_cost sched_hc t := by
      simp only [ready_jobs, List.mem_filter]
      constructor
      · apply arrived_between_implies_in_arrivals job_arrival arr_seq H_arrival_times_are_consistent j0 0 (t + 1)
          IN
        exact ⟨Nat.zero_le _, Nat.lt_succ_of_le PEND.1⟩
      · simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not]
        exact ⟨PEND, NOTSUSP⟩
    have NOTNONE := seq_min_exists (higher_eq_priority t) _ j0 IN0
    exact NOTNONE h_hp

include H_arrival_times_are_consistent H_priority_is_reflexive H_priority_is_transitive H_priority_is_total H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_work_conserving H_respects_priority H_respects_self_suspensions H_cost_of_j_does_not_decrease H_inflation_only_for_job_j in
theorem sched_susp_highercost_respects_policy :
    respects_JLDP_policy job_arrival inflated_job_cost job_suspension_duration arr_seq
      (sched_susp_highercost job_arrival arr_seq higher_eq_priority sched_susp
        job_suspension_duration inflated_job_cost) higher_eq_priority := by
  set sched_hc := sched_susp_highercost job_arrival arr_seq higher_eq_priority sched_susp
    job_suspension_duration inflated_job_cost with sched_hc_def
  intro j1 j2 t IN BACK SCHED
  obtain ⟨PEND, NOTSCHED, NOTSUSP⟩ := BACK
  have SCHED_EQ := sched_susp_highercost_uses_construction_function job_arrival job_cost arr_seq
    H_arrival_times_are_consistent higher_eq_priority H_priority_is_reflexive
    H_priority_is_transitive H_priority_is_total sched_susp
    H_jobs_come_from_arrival_sequence job_suspension_duration
    H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
    H_work_conserving H_respects_priority H_respects_self_suspensions j
    inflated_job_cost H_cost_of_j_does_not_decrease H_inflation_only_for_job_j t
  have SCHED_val : sched_hc t = some j2 := by
    simp only [scheduled_at] at SCHED; rwa [beq_iff_eq] at SCHED
  rw [sched_hc_def, SCHED_EQ, ← sched_hc_def] at SCHED_val
  -- ALL: hp computes minimum
  have ALL : ∀ j_hi j_lo, highest_priority_job job_arrival arr_seq higher_eq_priority
      job_suspension_duration inflated_job_cost sched_hc t = some j_hi →
      j_lo ∈ ready_jobs job_arrival arr_seq job_suspension_duration inflated_job_cost sched_hc t →
      higher_eq_priority t j_hi j_lo = true := by
    intro j_hi j_lo SOME INlo
    exact seq_min_computes_min (higher_eq_priority t)
      (fun x y z hxy hyz => H_priority_is_transitive t y x z hxy hyz)
      (ready_jobs job_arrival arr_seq job_suspension_duration inflated_job_cost sched_hc t)
      (by
        intro x y hx hy
        simp only [ready_jobs, List.mem_filter] at hx hy
        exact H_priority_is_total x y t
          (in_arrivals_implies_arrived job_arrival arr_seq H_arrival_times_are_consistent x 0 (t + 1) hx.1)
          (in_arrivals_implies_arrived job_arrival arr_seq H_arrival_times_are_consistent y 0 (t + 1) hy.1))
      j_hi j_lo SOME INlo
  have j1_IN_ready : j1 ∈ ready_jobs job_arrival arr_seq job_suspension_duration inflated_job_cost sched_hc t := by
    simp only [ready_jobs, List.mem_filter]
    constructor
    · apply arrived_between_implies_in_arrivals job_arrival arr_seq H_arrival_times_are_consistent j1 0 (t + 1)
        IN
      exact ⟨Nat.zero_le _, Nat.lt_succ_of_le PEND.1⟩
    · simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not]
      exact ⟨PEND, NOTSUSP⟩
  simp only [build_schedule] at SCHED_val
  cases h_hp : highest_priority_job job_arrival arr_seq higher_eq_priority job_suspension_duration
    inflated_job_cost sched_hc t with
  | none => simp [h_hp] at SCHED_val
  | some j_hp =>
    have HIGHER : higher_eq_priority t j_hp j1 = true := ALL j_hp j1 h_hp j1_IN_ready
    simp [h_hp] at SCHED_val
    cases h_susp : sched_susp t with
    | none =>
      simp [h_susp] at SCHED_val; subst SCHED_val; exact HIGHER
    | some j_s =>
      simp [h_susp] at SCHED_val
      split at SCHED_val
      · -- j2 = j_s with priority ≥ j_hp
        have h_eq := Option.some_injective _ SCHED_val; subst h_eq
        rename_i h_if
        exact H_priority_is_transitive t j_hp j_s j1 h_if.2 HIGHER
      · -- j2 = j_hp
        have h_eq := Option.some_injective _ SCHED_val; subst h_eq
        exact HIGHER

include H_arrival_times_are_consistent H_priority_is_reflexive H_priority_is_transitive H_priority_is_total H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_work_conserving H_respects_priority H_respects_self_suspensions H_cost_of_j_does_not_decrease H_inflation_only_for_job_j in
theorem sched_susp_highercost_respects_self_suspensions :
    respects_self_suspensions job_arrival inflated_job_cost job_suspension_duration
      (sched_susp_highercost job_arrival arr_seq higher_eq_priority sched_susp
        job_suspension_duration inflated_job_cost) := by
  set sched_hc := sched_susp_highercost job_arrival arr_seq higher_eq_priority sched_susp
    job_suspension_duration inflated_job_cost with sched_hc_def
  intro j0 t SCHED SUSP
  have SCHED_EQ := sched_susp_highercost_uses_construction_function job_arrival job_cost arr_seq
    H_arrival_times_are_consistent higher_eq_priority H_priority_is_reflexive
    H_priority_is_transitive H_priority_is_total sched_susp
    H_jobs_come_from_arrival_sequence job_suspension_duration
    H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
    H_work_conserving H_respects_priority H_respects_self_suspensions j
    inflated_job_cost H_cost_of_j_does_not_decrease H_inflation_only_for_job_j t
  have SCHED_val : sched_hc t = some j0 := by
    simp only [scheduled_at] at SCHED; rwa [beq_iff_eq] at SCHED
  rw [sched_hc_def, SCHED_EQ, ← sched_hc_def] at SCHED_val
  simp only [build_schedule] at SCHED_val
  cases h_hp : highest_priority_job job_arrival arr_seq higher_eq_priority job_suspension_duration
    inflated_job_cost sched_hc t with
  | none => simp [h_hp] at SCHED_val
  | some j_hp =>
    have IN : j_hp ∈ ready_jobs job_arrival arr_seq job_suspension_duration inflated_job_cost sched_hc t :=
      seq_min_in_seq _ _ _ h_hp
    have NOTSUSP_hp : ¬ suspended_at job_arrival inflated_job_cost job_suspension_duration sched_hc j_hp t := by
      simp only [ready_jobs, List.mem_filter, Bool.and_eq_true, decide_eq_true_eq,
        Bool.not_eq_true', decide_eq_false_iff_not] at IN
      exact IN.2.2
    simp [h_hp] at SCHED_val
    cases h_susp : sched_susp t with
    | none =>
      simp [h_susp] at SCHED_val
      subst SCHED_val; exact NOTSUSP_hp SUSP
    | some j_s =>
      simp [h_susp] at SCHED_val
      split at SCHED_val
      · have h_eq := Option.some_injective _ SCHED_val; subst h_eq
        rename_i h_if
        exact h_if.1.2 SUSP
      · have h_eq := Option.some_injective _ SCHED_val; subst h_eq
        exact NOTSUSP_hp SUSP

end ScheduleIsValid

section SchedulingInvariant

section InductiveStep

variable (t : Time)
variable (H_j_has_not_completed : ¬ completed_by job_cost sched_susp j t)

variable (H_schedules_are_the_same :
  ∀ k any_j,
    k < t →
    scheduled_at sched_susp any_j k =
    scheduled_at
      (sched_susp_highercost job_arrival arr_seq higher_eq_priority sched_susp
        job_suspension_duration inflated_job_cost)
      any_j k)

variable (k : Time)
variable (H_k_before_t : k ≤ t)

include H_arrival_times_are_consistent H_priority_is_reflexive H_priority_is_transitive H_priority_is_total H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_work_conserving H_respects_priority H_respects_self_suspensions H_cost_of_j_does_not_decrease H_inflation_only_for_job_j H_j_has_not_completed H_schedules_are_the_same H_k_before_t in
theorem sched_susp_highercost_same_completion :
    ∀ any_j,
      completed_by job_cost sched_susp any_j k =
      completed_by inflated_job_cost
        (sched_susp_highercost job_arrival arr_seq higher_eq_priority sched_susp
          job_suspension_duration inflated_job_cost)
        any_j k := by
  set sched_hc := sched_susp_highercost job_arrival arr_seq higher_eq_priority sched_susp
    job_suspension_duration inflated_job_cost with sched_hc_def
  -- Key: services are the same up to k because schedules agree before t and k ≤ t
  have SERV_at : ∀ any_j0 i, i < k → service_at sched_susp any_j0 i = service_at sched_hc any_j0 i := by
    intro any_j0 i hi
    simp only [service_at]
    have hi_lt_t : i < t := Nat.lt_of_lt_of_le hi H_k_before_t
    rw [H_schedules_are_the_same i any_j0 hi_lt_t]
  have SERV : ∀ any_j0, service sched_susp any_j0 k = service sched_hc any_j0 k := by
    intro any_j0
    simp only [service, service_during]
    apply Finset.sum_congr rfl
    intro i hi; rw [Finset.mem_Ico] at hi
    exact SERV_at any_j0 i hi.2
  -- Now prove the Prop equality
  intro any_j
  apply propext
  simp only [completed_by]
  constructor
  · -- Forward: job_cost any_j ≤ service sched_susp any_j k → inflated_job_cost any_j ≤ service sched_hc any_j k
    intro COMPs
    by_cases h_eq : any_j = j
    · -- any_j = j: contradiction with H_j_has_not_completed
      subst h_eq
      exfalso; apply H_j_has_not_completed
      exact completion_monotonic job_cost sched_susp _ k t H_k_before_t COMPs
    · -- any_j ≠ j: inflated_job_cost = job_cost, and service is the same
      rw [H_inflation_only_for_job_j any_j h_eq, ← SERV]
      exact COMPs
  · -- Backward: inflated_job_cost any_j ≤ service sched_hc any_j k → job_cost any_j ≤ service sched_susp any_j k
    intro COMPw
    by_cases h_eq : any_j = j
    · subst h_eq
      calc job_cost _ ≤ inflated_job_cost _ := H_cost_of_j_does_not_decrease
        _ ≤ service sched_hc _ k := COMPw
        _ = service sched_susp _ k := (SERV _).symm
    · rw [← H_inflation_only_for_job_j any_j h_eq]
      calc inflated_job_cost any_j ≤ service sched_hc any_j k := COMPw
        _ = service sched_susp any_j k := (SERV any_j).symm

include H_arrival_times_are_consistent H_priority_is_reflexive H_priority_is_transitive H_priority_is_total H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_work_conserving H_respects_priority H_respects_self_suspensions H_cost_of_j_does_not_decrease H_inflation_only_for_job_j H_j_has_not_completed H_schedules_are_the_same H_k_before_t in
theorem sched_susp_highercost_same_time_after_last_exec :
    ∀ any_j,
      time_after_last_execution job_arrival sched_susp any_j k =
      time_after_last_execution job_arrival
        (sched_susp_highercost job_arrival arr_seq higher_eq_priority sched_susp
          job_suspension_duration inflated_job_cost)
        any_j k := by
  set sched_hc := sched_susp_highercost job_arrival arr_seq higher_eq_priority sched_susp
    job_suspension_duration inflated_job_cost with sched_hc_def
  intro any_j
  simp only [time_after_last_execution]
  -- Show scheduled_before is the same
  have IH_at : ∀ i, i < k → scheduled_at sched_susp any_j i = scheduled_at sched_hc any_j i := by
    intro i hi
    exact H_schedules_are_the_same i any_j (Nat.lt_of_lt_of_le hi H_k_before_t)
  have EX_same : scheduled_before sched_susp any_j k = scheduled_before sched_hc any_j k := by
    simp only [scheduled_before]
    congr 1; apply propext
    constructor
    · rintro ⟨⟨t0, ht0⟩, hsched⟩
      exact ⟨⟨t0, ht0⟩, by rw [← IH_at t0 ht0]; exact hsched⟩
    · rintro ⟨⟨t0, ht0⟩, hsched⟩
      exact ⟨⟨t0, ht0⟩, by rw [IH_at t0 ht0]; exact hsched⟩
  rw [EX_same]
  split
  · rename_i h_sb
    -- Show last_time_scheduled is the same
    simp only [last_time_scheduled, max_nat_cond]
    have h_filter_eq : List.filter (fun t0 => scheduled_at sched_susp any_j t0) (values_between 0 k) =
                       List.filter (fun t0 => scheduled_at sched_hc any_j t0) (values_between 0 k) := by
      apply List.filter_congr
      intro i hi
      have hv := (mem_values_between 0 k i).mp hi
      rw [IH_at i hv.2]
    rw [h_filter_eq]
  · rfl

include H_arrival_times_are_consistent H_priority_is_reflexive H_priority_is_transitive H_priority_is_total H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_work_conserving H_respects_priority H_respects_self_suspensions H_cost_of_j_does_not_decrease H_inflation_only_for_job_j H_j_has_not_completed H_schedules_are_the_same H_k_before_t in
theorem sched_susp_highercost_same_suspension_duration :
    ∀ any_j,
      has_arrived job_arrival any_j k →
      suspension_duration job_arrival job_suspension_duration sched_susp any_j k =
      suspension_duration job_arrival job_suspension_duration
        (sched_susp_highercost job_arrival arr_seq higher_eq_priority sched_susp
          job_suspension_duration inflated_job_cost)
        any_j k := by
  set sched_hc := sched_susp_highercost job_arrival arr_seq higher_eq_priority sched_susp
    job_suspension_duration inflated_job_cost with sched_hc_def
  intro any_j ARR
  simp only [suspension_duration]
  -- Need to show: next_suspension any_j (service sched_susp any_j (tae sched_susp any_j k)) =
  --               next_suspension any_j (service sched_hc any_j (tae sched_hc any_j k))
  -- By same_time_after_last_exec, tae is the same
  have TAE := sched_susp_highercost_same_time_after_last_exec job_arrival job_cost arr_seq
    H_arrival_times_are_consistent higher_eq_priority H_priority_is_reflexive
    H_priority_is_transitive H_priority_is_total sched_susp
    H_jobs_come_from_arrival_sequence job_suspension_duration
    H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
    H_work_conserving H_respects_priority H_respects_self_suspensions j
    inflated_job_cost H_cost_of_j_does_not_decrease H_inflation_only_for_job_j
    t H_j_has_not_completed H_schedules_are_the_same k H_k_before_t any_j
  rw [TAE]
  -- Now show service up to the same tae point is the same
  -- tae sched_hc any_j k ≤ k ≤ t, so all time points before tae are < t
  -- and thus service_at agrees
  congr 1
  set tae_val := time_after_last_execution job_arrival sched_hc any_j k
  have tae_le_k : tae_val ≤ k := by
    exact last_execution_bounded_by_identity job_arrival sched_hc
      (sched_susp_highercost_jobs_must_arrive_to_execute job_arrival job_cost arr_seq
        H_arrival_times_are_consistent higher_eq_priority H_priority_is_reflexive
        H_priority_is_transitive H_priority_is_total sched_susp
        H_jobs_come_from_arrival_sequence job_suspension_duration
        H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
        H_work_conserving H_respects_priority H_respects_self_suspensions j
        inflated_job_cost H_cost_of_j_does_not_decrease H_inflation_only_for_job_j)
      any_j k ARR
  simp only [service, service_during]
  apply Finset.sum_congr rfl
  intro i hi; rw [Finset.mem_Ico] at hi
  simp only [service_at]
  have hi_lt_t : i < t := Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hi.2 tae_le_k) H_k_before_t
  rw [H_schedules_are_the_same i any_j hi_lt_t]

include H_arrival_times_are_consistent H_priority_is_reflexive H_priority_is_transitive H_priority_is_total H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_work_conserving H_respects_priority H_respects_self_suspensions H_cost_of_j_does_not_decrease H_inflation_only_for_job_j H_j_has_not_completed H_schedules_are_the_same H_k_before_t in
theorem sched_susp_highercost_same_suspension :
    ∀ any_j,
      has_arrived job_arrival any_j k →
      suspended_at job_arrival job_cost job_suspension_duration sched_susp any_j k =
      suspended_at job_arrival inflated_job_cost job_suspension_duration
        (sched_susp_highercost job_arrival arr_seq higher_eq_priority sched_susp
          job_suspension_duration inflated_job_cost)
        any_j k := by
  set sched_hc := sched_susp_highercost job_arrival arr_seq higher_eq_priority sched_susp
    job_suspension_duration inflated_job_cost with sched_hc_def
  intro any_j ARR
  simp only [suspended_at]
  -- Use same_completion to rewrite completed_by
  have COMP := sched_susp_highercost_same_completion job_arrival job_cost arr_seq
    H_arrival_times_are_consistent higher_eq_priority H_priority_is_reflexive
    H_priority_is_transitive H_priority_is_total sched_susp
    H_jobs_come_from_arrival_sequence job_suspension_duration
    H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
    H_work_conserving H_respects_priority H_respects_self_suspensions j
    inflated_job_cost H_cost_of_j_does_not_decrease H_inflation_only_for_job_j
    t H_j_has_not_completed H_schedules_are_the_same k H_k_before_t any_j
  -- Use same_time_after_last_exec
  have TAE := sched_susp_highercost_same_time_after_last_exec job_arrival job_cost arr_seq
    H_arrival_times_are_consistent higher_eq_priority H_priority_is_reflexive
    H_priority_is_transitive H_priority_is_total sched_susp
    H_jobs_come_from_arrival_sequence job_suspension_duration
    H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
    H_work_conserving H_respects_priority H_respects_self_suspensions j
    inflated_job_cost H_cost_of_j_does_not_decrease H_inflation_only_for_job_j
    t H_j_has_not_completed H_schedules_are_the_same k H_k_before_t any_j
  -- Use same_suspension_duration
  have SUSP_DUR := sched_susp_highercost_same_suspension_duration job_arrival job_cost arr_seq
    H_arrival_times_are_consistent higher_eq_priority H_priority_is_reflexive
    H_priority_is_transitive H_priority_is_total sched_susp
    H_jobs_come_from_arrival_sequence job_suspension_duration
    H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
    H_work_conserving H_respects_priority H_respects_self_suspensions j
    inflated_job_cost H_cost_of_j_does_not_decrease H_inflation_only_for_job_j
    t H_j_has_not_completed H_schedules_are_the_same k H_k_before_t any_j ARR
  -- Now rewrite all three components
  rw [COMP] at *
  rw [TAE, SUSP_DUR]

include H_arrival_times_are_consistent H_priority_is_reflexive H_priority_is_transitive H_priority_is_total H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_work_conserving H_respects_priority H_respects_self_suspensions H_cost_of_j_does_not_decrease H_inflation_only_for_job_j H_j_has_not_completed H_schedules_are_the_same H_k_before_t in
theorem sched_susp_highercost_same_schedule :
    ∀ any_j,
      scheduled_at sched_susp any_j k =
      scheduled_at
        (sched_susp_highercost job_arrival arr_seq higher_eq_priority sched_susp
          job_suspension_duration inflated_job_cost)
        any_j k := by
  set sched_hc := sched_susp_highercost job_arrival arr_seq higher_eq_priority sched_susp
    job_suspension_duration inflated_job_cost with sched_hc_def
  suffices h_eq : sched_susp k = sched_hc k by
    intro any_j; simp only [scheduled_at]; rw [h_eq]
  have LEMMAcomp : ∀ any_j,
      (completed_by job_cost sched_susp any_j k) =
      (completed_by inflated_job_cost sched_hc any_j k) :=
    sched_susp_highercost_same_completion job_arrival job_cost arr_seq
      H_arrival_times_are_consistent higher_eq_priority H_priority_is_reflexive
      H_priority_is_transitive H_priority_is_total sched_susp
      H_jobs_come_from_arrival_sequence job_suspension_duration
      H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
      H_work_conserving H_respects_priority H_respects_self_suspensions j
      inflated_job_cost H_cost_of_j_does_not_decrease H_inflation_only_for_job_j
      t H_j_has_not_completed H_schedules_are_the_same k H_k_before_t
  have LEMMAsusp : ∀ any_j, has_arrived job_arrival any_j k →
      (suspended_at job_arrival job_cost job_suspension_duration sched_susp any_j k) =
      (suspended_at job_arrival inflated_job_cost job_suspension_duration sched_hc any_j k) :=
    sched_susp_highercost_same_suspension job_arrival job_cost arr_seq
      H_arrival_times_are_consistent higher_eq_priority H_priority_is_reflexive
      H_priority_is_transitive H_priority_is_total sched_susp
      H_jobs_come_from_arrival_sequence job_suspension_duration
      H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
      H_work_conserving H_respects_priority H_respects_self_suspensions j
      inflated_job_cost H_cost_of_j_does_not_decrease H_inflation_only_for_job_j
      t H_j_has_not_completed H_schedules_are_the_same k H_k_before_t
  rw [sched_hc_def, sched_susp_highercost_uses_construction_function job_arrival job_cost arr_seq
    H_arrival_times_are_consistent higher_eq_priority H_priority_is_reflexive
    H_priority_is_transitive H_priority_is_total sched_susp
    H_jobs_come_from_arrival_sequence job_suspension_duration
    H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
    H_work_conserving H_respects_priority H_respects_self_suspensions j
    inflated_job_cost H_cost_of_j_does_not_decrease H_inflation_only_for_job_j k, ← sched_hc_def]
  -- Goal: sched_susp k = build_schedule ... sched_hc k
  -- Case split then compute build_schedule value
  cases h_hp : highest_priority_job job_arrival arr_seq higher_eq_priority job_suspension_duration
    inflated_job_cost sched_hc k with
  | none =>
    cases h_susp : sched_susp k with
    | none =>
      show none = build_schedule job_arrival arr_seq higher_eq_priority sched_susp
        job_suspension_duration inflated_job_cost sched_hc k
      simp [build_schedule, h_hp]
    | some j_s =>
      exfalso
      have h_sched_s : scheduled_at sched_susp j_s k = true := by
        simp only [scheduled_at]; rw [h_susp]; simp
      have ARR : has_arrived job_arrival j_s k := H_jobs_must_arrive_to_execute j_s k h_sched_s
      have ARR_in : arrives_in arr_seq j_s := H_jobs_come_from_arrival_sequence j_s k h_sched_s
      have NOTCOMP_hc : ¬ completed_by inflated_job_cost sched_hc j_s k := by
        rw [← LEMMAcomp]
        exact scheduled_implies_not_completed job_cost sched_susp j_s H_completed_jobs_dont_execute k h_sched_s
      have NOTSUSP_hc : ¬ suspended_at job_arrival inflated_job_cost job_suspension_duration sched_hc j_s k := by
        rw [← LEMMAsusp j_s ARR]
        exact H_respects_self_suspensions j_s k h_sched_s
      have IN : j_s ∈ ready_jobs job_arrival arr_seq job_suspension_duration inflated_job_cost sched_hc k := by
        simp only [ready_jobs, List.mem_filter]
        constructor
        · exact arrived_between_implies_in_arrivals job_arrival arr_seq H_arrival_times_are_consistent j_s 0 (k + 1)
            ARR_in ⟨Nat.zero_le _, Nat.lt_succ_of_le ARR⟩
        · simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not]
          exact ⟨⟨ARR, NOTCOMP_hc⟩, NOTSUSP_hc⟩
      exact (seq_min_exists (higher_eq_priority k) _ j_s IN) h_hp
  | some j_hp =>
    have IN_hp : j_hp ∈ ready_jobs job_arrival arr_seq job_suspension_duration inflated_job_cost sched_hc k :=
      seq_min_in_seq _ _ _ h_hp
    have hp_props : pending job_arrival inflated_job_cost sched_hc j_hp k ∧
        ¬ suspended_at job_arrival inflated_job_cost job_suspension_duration sched_hc j_hp k := by
      simp only [ready_jobs, List.mem_filter, Bool.and_eq_true, decide_eq_true_eq,
        Bool.not_eq_true', decide_eq_false_iff_not] at IN_hp
      exact IN_hp.2
    have ARRhp : has_arrived job_arrival j_hp k := hp_props.1.1
    have ARRhp_in : arrives_in arr_seq j_hp := by
      simp only [ready_jobs, List.mem_filter] at IN_hp
      exact in_arrivals_implies_arrived job_arrival arr_seq H_arrival_times_are_consistent j_hp 0 (k + 1) IN_hp.1
    cases h_susp : sched_susp k with
    | none =>
      exfalso
      have NOTCOMPhp : ¬ completed_by job_cost sched_susp j_hp k := by
        rw [LEMMAcomp]; exact hp_props.1.2
      have NOTSCHEDhp : ¬ scheduled_at sched_susp j_hp k = true := by
        simp only [scheduled_at]; rw [h_susp]; simp
      have NOTSUSPhp : ¬ suspended_at job_arrival job_cost job_suspension_duration sched_susp j_hp k := by
        rw [LEMMAsusp j_hp ARRhp]; exact hp_props.2
      have BACK : backlogged job_arrival job_cost job_suspension_duration sched_susp j_hp k :=
        ⟨⟨ARRhp, NOTCOMPhp⟩, NOTSCHEDhp, NOTSUSPhp⟩
      obtain ⟨j', h_sched_j'⟩ := H_work_conserving j_hp k ARRhp_in BACK
      simp only [scheduled_at] at h_sched_j'; rw [h_susp] at h_sched_j'; simp at h_sched_j'
    | some j_s =>
      -- Show build_schedule returns some j_s (because the if-condition is true)
      have h_sched_s : scheduled_at sched_susp j_s k = true := by
        simp only [scheduled_at]; rw [h_susp]; simp
      have ARR_s : has_arrived job_arrival j_s k := H_jobs_must_arrive_to_execute j_s k h_sched_s
      have NOTCOMP_hc : ¬ completed_by inflated_job_cost sched_hc j_s k := by
        rw [← LEMMAcomp]
        exact scheduled_implies_not_completed job_cost sched_susp j_s H_completed_jobs_dont_execute k h_sched_s
      have NOTSUSP_hc : ¬ suspended_at job_arrival inflated_job_cost job_suspension_duration sched_hc j_s k := by
        rw [← LEMMAsusp j_s ARR_s]
        exact H_respects_self_suspensions j_s k h_sched_s
      have h_prio : higher_eq_priority k j_s j_hp = true := by
        by_cases h_eq : j_s = j_hp
        · subst h_eq; exact H_priority_is_reflexive k j_s
        · have NOTCOMPhp : ¬ completed_by job_cost sched_susp j_hp k := by
            rw [LEMMAcomp]; exact hp_props.1.2
          have NOTSCHEDhp : ¬ scheduled_at sched_susp j_hp k = true := by
            intro h_sched
            exact absurd (only_one_job_scheduled sched_susp j_s j_hp k h_sched_s h_sched) h_eq
          have NOTSUSPhp : ¬ suspended_at job_arrival job_cost job_suspension_duration sched_susp j_hp k := by
            rw [LEMMAsusp j_hp ARRhp]; exact hp_props.2
          exact H_respects_priority j_hp j_s k ARRhp_in
            ⟨⟨ARRhp, NOTCOMPhp⟩, NOTSCHEDhp, NOTSUSPhp⟩ h_sched_s
      have h_cond : ((decide (pending job_arrival inflated_job_cost sched_hc j_s k) &&
          !decide (suspended_at job_arrival inflated_job_cost job_suspension_duration sched_hc j_s k)) &&
          higher_eq_priority k j_s j_hp) = true := by
        simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not]
        exact ⟨⟨⟨ARR_s, NOTCOMP_hc⟩, NOTSUSP_hc⟩, h_prio⟩
      show some j_s = build_schedule job_arrival arr_seq higher_eq_priority sched_susp
        job_suspension_duration inflated_job_cost sched_hc k
      simp only [build_schedule, h_hp, h_susp]; simp [h_cond]

end InductiveStep

include H_arrival_times_are_consistent H_priority_is_reflexive H_priority_is_transitive H_priority_is_total H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_work_conserving H_respects_priority H_respects_self_suspensions H_cost_of_j_does_not_decrease H_inflation_only_for_job_j in
theorem scheduled_in_susp_iff_scheduled_in_wcet :
    ∀ t any_j,
      ¬ completed_by job_cost sched_susp j t →
      scheduled_at sched_susp any_j t =
      scheduled_at
        (sched_susp_highercost job_arrival arr_seq higher_eq_priority sched_susp
          job_suspension_duration inflated_job_cost)
        any_j t := by
  intro t
  induction t using Nat.strongRecOn with
  | _ t IH =>
    intro any_j NOTCOMP
    -- Build the induction hypothesis for sched_susp_highercost_same_schedule
    have IH' : ∀ k any_j, k < t →
        scheduled_at sched_susp any_j k =
        scheduled_at (sched_susp_highercost job_arrival arr_seq higher_eq_priority sched_susp
          job_suspension_duration inflated_job_cost) any_j k := by
      intro k any_j hlt
      exact IH k hlt any_j (fun COMPk =>
        NOTCOMP (completion_monotonic job_cost sched_susp j k t (Nat.le_of_lt hlt) COMPk))
    exact sched_susp_highercost_same_schedule job_arrival job_cost arr_seq
      H_arrival_times_are_consistent higher_eq_priority H_priority_is_reflexive
      H_priority_is_transitive H_priority_is_total sched_susp
      H_jobs_come_from_arrival_sequence job_suspension_duration
      H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
      H_work_conserving H_respects_priority H_respects_self_suspensions j
      inflated_job_cost H_cost_of_j_does_not_decrease H_inflation_only_for_job_j
      t NOTCOMP IH' t (Nat.le_refl t) any_j

end SchedulingInvariant

section ComparingResponseTimes

variable (H_cost_j_positive : job_cost j > 0)

variable (r : Time)
variable (H_response_time_bound_in_sched_susp :
  is_response_time_bound_of_job job_arrival job_cost sched_susp j r)
variable (H_response_time_bound_is_tight :
  ∀ r', is_response_time_bound_of_job job_arrival job_cost sched_susp j r' → r ≤ r')

variable (R : Time)
variable (H_response_time_bound_in_sched_susp_highercost :
  is_response_time_bound_of_job job_arrival inflated_job_cost
    (sched_susp_highercost job_arrival arr_seq higher_eq_priority sched_susp
      job_suspension_duration inflated_job_cost)
    j R)

include H_arrival_times_are_consistent H_priority_is_reflexive H_priority_is_transitive H_priority_is_total H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_work_conserving H_respects_priority H_respects_self_suspensions H_cost_of_j_does_not_decrease H_inflation_only_for_job_j H_cost_j_positive H_response_time_bound_in_sched_susp H_response_time_bound_is_tight H_response_time_bound_in_sched_susp_highercost in
theorem sched_susp_highercost_same_service_for_j :
    ∀ t,
      t ≤ job_arrival j + r →
      service sched_susp j t =
      service
        (sched_susp_highercost job_arrival arr_seq higher_eq_priority sched_susp
          job_suspension_duration inflated_job_cost)
        j t := by
  set sched_hc := sched_susp_highercost job_arrival arr_seq higher_eq_priority sched_susp
    job_suspension_duration inflated_job_cost with sched_hc_def
  have IFF := scheduled_in_susp_iff_scheduled_in_wcet job_arrival job_cost arr_seq
    H_arrival_times_are_consistent higher_eq_priority H_priority_is_reflexive
    H_priority_is_transitive H_priority_is_total sched_susp
    H_jobs_come_from_arrival_sequence job_suspension_duration
    H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
    H_work_conserving H_respects_priority H_respects_self_suspensions j
    inflated_job_cost H_cost_of_j_does_not_decrease H_inflation_only_for_job_j
  intro t
  induction t with
  | zero => intro _; simp only [service, service_during, Finset.Ico_self, Finset.sum_empty]
  | succ n IHn =>
    intro LT
    have IHn_applied := IHn (Nat.le_of_succ_le LT)
    -- Show service equality at n+1 = service at n + service_at n
    have h_not_comp : ¬ completed_by job_cost sched_susp j n := by
      intro COMPn
      have h_arr_le : job_arrival j ≤ n := by
        by_contra h_not
        push_neg at h_not
        have h_zero : service sched_susp j n = 0 := by
          simp only [service, service_during]
          apply Finset.sum_eq_zero
          intro i hi; rw [Finset.mem_Ico] at hi
          exact service_before_job_arrival_zero job_arrival sched_susp H_jobs_must_arrive_to_execute j i
            (Nat.lt_trans hi.2 h_not)
        simp only [completed_by] at COMPn; simp only [Time] at *; omega
      have h_resp : is_response_time_bound_of_job job_arrival job_cost sched_susp j (n - job_arrival j) := by
        show completed_by job_cost sched_susp j (job_arrival j + (n - job_arrival j))
        rw [Nat.add_sub_cancel' h_arr_le]; exact COMPn
      have h_tight := H_response_time_bound_is_tight (n - job_arrival j) h_resp
      simp only [Time] at *; omega
    have h_sa_eq : service_at sched_susp j n = service_at sched_hc j n := by
      simp only [service_at]
      rw [IFF n j h_not_comp]
    simp only [service, service_during]
    rw [Finset.sum_Ico_succ_top (Nat.zero_le n), Finset.sum_Ico_succ_top (Nat.zero_le n)]
    simp only [service, service_during] at IHn_applied
    rw [IHn_applied, h_sa_eq]

include H_arrival_times_are_consistent H_priority_is_reflexive H_priority_is_transitive H_priority_is_total H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_work_conserving H_respects_priority H_respects_self_suspensions H_cost_of_j_does_not_decrease H_inflation_only_for_job_j H_cost_j_positive H_response_time_bound_in_sched_susp H_response_time_bound_is_tight H_response_time_bound_in_sched_susp_highercost in
theorem sched_susp_highercost_r_le_R : r ≤ R := by
  set sched_hc := sched_susp_highercost job_arrival arr_seq higher_eq_priority sched_susp
    job_suspension_duration inflated_job_cost with sched_hc_def
  have SAME := sched_susp_highercost_same_service_for_j job_arrival job_cost arr_seq
    H_arrival_times_are_consistent higher_eq_priority H_priority_is_reflexive
    H_priority_is_transitive H_priority_is_total sched_susp
    H_jobs_come_from_arrival_sequence job_suspension_duration
    H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
    H_work_conserving H_respects_priority H_respects_self_suspensions j
    inflated_job_cost H_cost_of_j_does_not_decrease H_inflation_only_for_job_j
    H_cost_j_positive r H_response_time_bound_in_sched_susp
    H_response_time_bound_is_tight R H_response_time_bound_in_sched_susp_highercost
  -- Proof by contradiction: assume R < r
  by_contra h_not
  push_neg at h_not
  -- R < r
  -- service_hc j (arr_j + R) ≥ inflated_job_cost j (from H_response_time_bound_in_sched_susp_highercost)
  have h_resp_hc : inflated_job_cost j ≤ service sched_hc j (job_arrival j + R) :=
    H_response_time_bound_in_sched_susp_highercost
  -- service_susp j (arr_j + R) = service_hc j (arr_j + R) (by SAME, since arr_j + R ≤ arr_j + r)
  have h_same_R : service sched_susp j (job_arrival j + R) = service sched_hc j (job_arrival j + R) :=
    SAME (job_arrival j + R) (Nat.add_le_add_left (Nat.le_of_lt h_not) (job_arrival j))
  -- So job_cost j ≤ inflated_job_cost j ≤ service_susp j (arr_j + R)
  have h_completed : completed_by job_cost sched_susp j (job_arrival j + R) := by
    show job_cost j ≤ service sched_susp j (job_arrival j + R)
    calc job_cost j ≤ inflated_job_cost j := H_cost_of_j_does_not_decrease
      _ ≤ service sched_hc j (job_arrival j + R) := h_resp_hc
      _ = service sched_susp j (job_arrival j + R) := h_same_R.symm
  -- By TIGHT: r ≤ R
  have h_tight : r ≤ R := H_response_time_bound_is_tight R h_completed
  exact absurd h_not (Nat.not_lt.mpr h_tight)

include H_arrival_times_are_consistent H_priority_is_reflexive H_priority_is_transitive H_priority_is_total H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_work_conserving H_respects_priority H_respects_self_suspensions H_cost_of_j_does_not_decrease H_inflation_only_for_job_j H_response_time_bound_in_sched_susp_highercost in
theorem R_bounds_inflated_cost : R ≥ inflated_job_cost j := by
  set sched_hc := sched_susp_highercost job_arrival arr_seq higher_eq_priority sched_susp
    job_suspension_duration inflated_job_cost with sched_hc_def
  -- Step 1: inflated_job_cost j ≤ service sched_hc j (job_arrival j + R)
  -- This is exactly H_response_time_bound_in_sched_susp_highercost (unfolding is_response_time_bound_of_job = completed_by)
  have h1 : inflated_job_cost j ≤ service sched_hc j (job_arrival j + R) :=
    H_response_time_bound_in_sched_susp_highercost
  -- Step 2: service sched_hc j (job_arrival j + R) ≤ R
  have h2 : service sched_hc j (job_arrival j + R) ≤ R := by
    simp only [service, service_during]
    rw [ignore_service_before_arrival job_arrival sched_hc
      (sched_susp_highercost_jobs_must_arrive_to_execute job_arrival job_cost arr_seq
        H_arrival_times_are_consistent higher_eq_priority H_priority_is_reflexive
        H_priority_is_transitive H_priority_is_total sched_susp
        H_jobs_come_from_arrival_sequence job_suspension_duration
        H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
        H_work_conserving H_respects_priority H_respects_self_suspensions j
        inflated_job_cost H_cost_of_j_does_not_decrease H_inflation_only_for_job_j)
      j 0 (job_arrival j + R) (Nat.zero_le _) (Nat.le_add_right _ _)]
    exact cumulative_service_le_delta sched_hc j (job_arrival j) R
  exact le_trans h1 h2

include H_arrival_times_are_consistent H_priority_is_reflexive H_priority_is_transitive H_priority_is_total H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_work_conserving H_respects_priority H_respects_self_suspensions H_cost_of_j_does_not_decrease H_inflation_only_for_job_j H_cost_j_positive H_response_time_bound_in_sched_susp H_response_time_bound_is_tight H_response_time_bound_in_sched_susp_highercost in
theorem sched_susp_highercost_incurs_more_interference :
    r - job_cost j ≤ R - inflated_job_cost j := by
  set arr_j := job_arrival j
  set sched_hc := sched_susp_highercost job_arrival arr_seq higher_eq_priority sched_susp
    job_suspension_duration inflated_job_cost with sched_hc_def
  -- Key facts
  have GECOST : R ≥ inflated_job_cost j :=
    R_bounds_inflated_cost job_arrival job_cost arr_seq H_arrival_times_are_consistent
      higher_eq_priority H_priority_is_reflexive H_priority_is_transitive H_priority_is_total
      sched_susp H_jobs_come_from_arrival_sequence job_suspension_duration
      H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_work_conserving
      H_respects_priority H_respects_self_suspensions j inflated_job_cost
      H_cost_of_j_does_not_decrease H_inflation_only_for_job_j R
      H_response_time_bound_in_sched_susp_highercost
  have LEQ : r ≤ R :=
    sched_susp_highercost_r_le_R job_arrival job_cost arr_seq
      H_arrival_times_are_consistent higher_eq_priority H_priority_is_reflexive
      H_priority_is_transitive H_priority_is_total sched_susp
      H_jobs_come_from_arrival_sequence job_suspension_duration
      H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_work_conserving
      H_respects_priority H_respects_self_suspensions j inflated_job_cost
      H_cost_of_j_does_not_decrease H_inflation_only_for_job_j H_cost_j_positive r
      H_response_time_bound_in_sched_susp H_response_time_bound_is_tight R
      H_response_time_bound_in_sched_susp_highercost
  have SAME : ∀ t, t ≤ arr_j + r → service sched_susp j t = service sched_hc j t :=
    sched_susp_highercost_same_service_for_j job_arrival job_cost arr_seq
      H_arrival_times_are_consistent higher_eq_priority H_priority_is_reflexive
      H_priority_is_transitive H_priority_is_total sched_susp
      H_jobs_come_from_arrival_sequence job_suspension_duration
      H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_work_conserving
      H_respects_priority H_respects_self_suspensions j inflated_job_cost
      H_cost_of_j_does_not_decrease H_inflation_only_for_job_j H_cost_j_positive r
      H_response_time_bound_in_sched_susp H_response_time_bound_is_tight R
      H_response_time_bound_in_sched_susp_highercost
  -- service sched_susp j (arr_j + r) = job_cost j
  have Ss_eq : service sched_susp j (arr_j + r) = job_cost j := by
    have h_le : service sched_susp j (arr_j + r) ≤ job_cost j :=
      H_completed_jobs_dont_execute j (arr_j + r)
    have h_ge : job_cost j ≤ service sched_susp j (arr_j + r) :=
      H_response_time_bound_in_sched_susp
    exact le_antisymm h_le h_ge
  -- service sched_hc j (arr_j + r) = job_cost j (by SAME)
  have Sw_r_eq : service sched_hc j (arr_j + r) = job_cost j := by
    rw [← SAME (arr_j + r) (le_refl _)]; exact Ss_eq
  -- inflated_job_cost j ≤ service sched_hc j (arr_j + R) from response time bound
  have h_resp : inflated_job_cost j ≤ service sched_hc j (arr_j + R) :=
    H_response_time_bound_in_sched_susp_highercost
  -- Split: service 0 (arr_j + R) = service 0 (arr_j + r) + service_during (arr_j + r) (arr_j + R)
  have Sw_split : service sched_hc j (arr_j + R) =
      service sched_hc j (arr_j + r) + service_during sched_hc j (arr_j + r) (arr_j + R) := by
    simp only [service, service_during]
    rw [← Finset.sum_Ico_consecutive (f := fun i => service_at sched_hc j i)]
    · exact Nat.zero_le _
    · exact Nat.add_le_add_left LEQ arr_j
  -- service_during sched_hc j (arr_j + r) (arr_j + R) ≤ R - r
  have Sw_extra_le : service_during sched_hc j (arr_j + r) (arr_j + R) ≤ R - r := by
    have h := cumulative_service_le_delta sched_hc j (arr_j + r) (R - r)
    have h_eq : arr_j + r + (R - r) = arr_j + R := by
      simp only [Time] at *; omega
    rw [h_eq] at h; exact h
  -- inflated_job_cost j ≤ job_cost j + (R - r) from RESPw
  have inflated_le : inflated_job_cost j ≤ job_cost j + (R - r) := by
    have h1 := h_resp
    rw [Sw_split, Sw_r_eq] at h1
    -- h1 : inflated_job_cost j ≤ job_cost j + service_during ...
    -- Sw_extra_le : service_during ... ≤ R - r
    exact le_trans h1 (Nat.add_le_add_left Sw_extra_le _)
  -- Now conclude: r - job_cost j ≤ R - inflated_job_cost j
  -- inflated_le : inflated_job_cost j ≤ job_cost j + (R - r)
  -- GECOST : R ≥ inflated_job_cost j
  -- This means: inflated_job_cost j - job_cost j ≤ R - r
  -- So: r - job_cost j ≤ R - inflated_job_cost j
  simp only [Time] at *; omega

end ComparingResponseTimes

end ReductionProperties

end SustainabilitySingleCostProperties

end

end Prosa.Classic.Analysis.Uni.Susp.Sustainability.Singlecost.Reduction_properties
