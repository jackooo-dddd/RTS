-- Translated from: ../rt-proofs/classic/analysis/uni/susp/sustainability/allcosts/reduction_properties.v
import Prosa.Classic.Util.All
import Prosa.Classic.Model.Priority
import Prosa.Classic.Model.Arrival.Basic.Arrival_sequence
import Prosa.Classic.Model.Schedule.Uni.Response_time
import Prosa.Classic.Model.Schedule.Uni.Susp.Suspension_intervals
import Prosa.Classic.Model.Schedule.Uni.Susp.Schedule
import Prosa.Classic.Model.Schedule.Uni.Susp.Valid_schedule
import Prosa.Classic.Model.Schedule.Uni.Susp.Build_suspension_table
import Prosa.Classic.Model.Schedule.Uni.Susp.Platform
import Prosa.Classic.Analysis.Uni.Susp.Sustainability.Allcosts.Reduction
import Prosa.Classic.Model.Schedule.Uni.Transformation.Construction
import Prosa.Classic.Model.Suspension
import Prosa.Classic.Model.Schedule.Uni.Schedule
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

namespace Prosa.Classic.Analysis.Uni.Susp.Sustainability.Allcosts.Reduction_properties

open Prosa.Classic.Model.Time
open Prosa.Classic.Model.Schedule.Uni.Schedule
open Prosa.Classic.Model.Schedule.Uni.Susp.Suspension_intervals
open Prosa.Classic.Model.Schedule.Uni.Susp.Schedule
open Prosa.Classic.Model.Schedule.Uni.Susp.Platform.PlatformWithSuspensions
open Prosa.Classic.Model.Schedule.Uni.Susp.Valid_schedule
open Prosa.Classic.Model.Schedule.Uni.Susp.Build_suspension_table.SuspensionTableConstruction
open Prosa.Classic.Model.Schedule.Uni.Susp.Last_execution
open Prosa.Classic.Model.Schedule.Uni.Response_time.ResponseTime
open Prosa.Classic.Model.Schedule.Uni.Transformation.Construction.ScheduleConstruction
open Prosa.Classic.Model.Suspension
open Prosa.Classic.Model.Priority
open Prosa.Classic.Model.Arrival.Basic.Arrival_sequence
open Prosa.Classic.Analysis.Uni.Susp.Sustainability.Allcosts.Reduction.SustainabilityAllCosts
open Prosa.Classic.Util.Minmax
open Classical

attribute [local instance] propDecidable

noncomputable section

namespace SustainabilityAllCostsProperties

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

variable (R : Time)

variable (inflated_job_cost : Job → Time)

variable (H_job_costs_do_not_decrease :
  ∀ any_j, inflated_job_cost any_j ≥ job_cost any_j)

section PropertiesOfScheduleConstruction

include H_arrival_times_are_consistent H_priority_is_reflexive H_priority_is_transitive H_priority_is_total H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_work_conserving H_respects_priority H_respects_self_suspensions H_job_costs_do_not_decrease in
theorem sched_new_depends_only_on_service :
    ∀ sched1 sched2 t,
      (∀ j, service sched1 j t = service sched2 j t) →
      build_schedule job_arrival job_cost arr_seq higher_eq_priority
        sched_susp inflated_job_cost j R sched1 t =
      build_schedule job_arrival job_cost arr_seq higher_eq_priority
        sched_susp inflated_job_cost j R sched2 t := by
  intro sched1 sched2 t0 SAME
  simp only [build_schedule]
  -- Key helper: both schedules give same pending status
  have PEND_EQ : ∀ j0, pending job_arrival inflated_job_cost sched1 j0 t0 ↔
      pending job_arrival inflated_job_cost sched2 j0 t0 := by
    intro j0; simp only [pending, completed_by]; rw [SAME j0]
  -- Key helper: both schedules give same job_is_late status
  have LATE_EQ : ∀ j0, job_is_late job_cost sched_susp inflated_job_cost sched1 j0 t0 =
      job_is_late job_cost sched_susp inflated_job_cost sched2 j0 t0 := by
    intro j0; simp only [job_is_late]; rw [SAME j0]
  -- Show the late job lists are equal
  have FILT_LATE : jobs_that_are_late_or_scheduled_in_sched_susp job_arrival job_cost arr_seq sched_susp inflated_job_cost sched1 t0 =
      jobs_that_are_late_or_scheduled_in_sched_susp job_arrival job_cost arr_seq sched_susp inflated_job_cost sched2 t0 := by
    simp only [jobs_that_are_late_or_scheduled_in_sched_susp]
    apply List.filter_congr; intro j0 _
    -- filter condition: decide (pending ...) && (job_is_late ... || scheduled_at ...)
    have hp : decide (pending job_arrival inflated_job_cost sched1 j0 t0) =
        decide (pending job_arrival inflated_job_cost sched2 j0 t0) := by
      exact decide_eq_decide.mpr (PEND_EQ j0)
    rw [hp, LATE_EQ j0]
  -- Show the pending job lists are equal
  have FILT_PEND : pending_jobs job_arrival arr_seq inflated_job_cost sched1 t0 =
      pending_jobs job_arrival arr_seq inflated_job_cost sched2 t0 := by
    simp only [pending_jobs]
    apply List.filter_congr; intro j0 _
    exact decide_eq_decide.mpr (PEND_EQ j0)
  split
  · simp only [highest_priority_late_job]; rw [FILT_LATE]
  · simp only [highest_priority_job]; rw [FILT_PEND]

include H_arrival_times_are_consistent H_priority_is_reflexive H_priority_is_transitive H_priority_is_total H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_work_conserving H_respects_priority H_respects_self_suspensions H_job_costs_do_not_decrease in
theorem sched_new_uses_construction_function :
    ∀ t,
      sched_new job_arrival job_cost arr_seq higher_eq_priority
        sched_susp inflated_job_cost j R t =
      build_schedule job_arrival job_cost arr_seq higher_eq_priority
        sched_susp inflated_job_cost j R
        (sched_new job_arrival job_cost arr_seq higher_eq_priority
          sched_susp inflated_job_cost j R) t := by
  intro t0
  have DEP := @sched_new_depends_only_on_service Job _ job_arrival job_cost arr_seq
    H_arrival_times_are_consistent higher_eq_priority H_priority_is_reflexive
    H_priority_is_transitive H_priority_is_total sched_susp H_jobs_come_from_arrival_sequence
    job_suspension_duration H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
    H_work_conserving H_respects_priority H_respects_self_suspensions j R inflated_job_cost
    H_job_costs_do_not_decrease
  exact service_dependent_schedule_construction
    (fun sched_prefix t => build_schedule job_arrival job_cost arr_seq higher_eq_priority
      sched_susp inflated_job_cost j R sched_prefix t)
    (fun _ => none)
    DEP t0

end PropertiesOfScheduleConstruction

section BasicScheduleProperties

include H_arrival_times_are_consistent H_priority_is_reflexive H_priority_is_transitive H_priority_is_total H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_work_conserving H_respects_priority H_respects_self_suspensions H_job_costs_do_not_decrease in
theorem sched_new_jobs_come_from_arrival_sequence :
    jobs_come_from_arrival_sequence
      (sched_new job_arrival job_cost arr_seq higher_eq_priority
        sched_susp inflated_job_cost j R) arr_seq := by
  intro j0 t SCHEDn
  have hEQ : sched_new job_arrival job_cost arr_seq higher_eq_priority sched_susp inflated_job_cost j R t = some j0 := by
    simp only [scheduled_at] at SCHEDn; rwa [beq_iff_eq] at SCHEDn
  have USE := @sched_new_uses_construction_function Job _ job_arrival job_cost arr_seq
    H_arrival_times_are_consistent higher_eq_priority H_priority_is_reflexive
    H_priority_is_transitive H_priority_is_total sched_susp H_jobs_come_from_arrival_sequence
    job_suspension_duration H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
    H_work_conserving H_respects_priority H_respects_self_suspensions j R inflated_job_cost
    H_job_costs_do_not_decrease t
  rw [USE] at hEQ
  simp only [build_schedule] at hEQ
  by_cases hLT : t < job_arrival j + R
  · simp only [hLT, ↓reduceIte] at hEQ
    have hIN := seq_min_in_seq (higher_eq_priority t) _ j0 hEQ
    simp only [jobs_that_are_late_or_scheduled_in_sched_susp, List.mem_filter] at hIN
    exact in_arrivals_implies_arrived job_arrival arr_seq H_arrival_times_are_consistent j0 0 (t + 1) hIN.1
  · simp only [hLT, ↓reduceIte] at hEQ
    have hIN := seq_min_in_seq (higher_eq_priority t) _ j0 hEQ
    simp only [pending_jobs, List.mem_filter] at hIN
    exact in_arrivals_implies_arrived job_arrival arr_seq H_arrival_times_are_consistent j0 0 (t + 1) hIN.1

include H_arrival_times_are_consistent H_priority_is_reflexive H_priority_is_transitive H_priority_is_total H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_work_conserving H_respects_priority H_respects_self_suspensions H_job_costs_do_not_decrease in
theorem sched_new_jobs_must_arrive_to_execute :
    jobs_must_arrive_to_execute job_arrival
      (sched_new job_arrival job_cost arr_seq higher_eq_priority
        sched_susp inflated_job_cost j R) := by
  intro j0 t SCHEDn
  have hEQ : sched_new job_arrival job_cost arr_seq higher_eq_priority sched_susp inflated_job_cost j R t = some j0 := by
    simp only [scheduled_at] at SCHEDn; rwa [beq_iff_eq] at SCHEDn
  have USE := @sched_new_uses_construction_function Job _ job_arrival job_cost arr_seq
    H_arrival_times_are_consistent higher_eq_priority H_priority_is_reflexive
    H_priority_is_transitive H_priority_is_total sched_susp H_jobs_come_from_arrival_sequence
    job_suspension_duration H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
    H_work_conserving H_respects_priority H_respects_self_suspensions j R inflated_job_cost
    H_job_costs_do_not_decrease t
  rw [USE] at hEQ
  simp only [build_schedule] at hEQ
  by_cases hLT : t < job_arrival j + R
  · simp only [hLT, ↓reduceIte] at hEQ
    have hIN := seq_min_in_seq (higher_eq_priority t) _ j0 hEQ
    simp only [jobs_that_are_late_or_scheduled_in_sched_susp, List.mem_filter] at hIN
    have hPend := hIN.2
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hPend
    exact hPend.1.1
  · simp only [hLT, ↓reduceIte] at hEQ
    have hIN := seq_min_in_seq (higher_eq_priority t) _ j0 hEQ
    simp only [pending_jobs, List.mem_filter] at hIN
    have hPend := hIN.2
    simp only [decide_eq_true_eq] at hPend
    exact hPend.1

include H_arrival_times_are_consistent H_priority_is_reflexive H_priority_is_transitive H_priority_is_total H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_work_conserving H_respects_priority H_respects_self_suspensions H_job_costs_do_not_decrease in
theorem sched_new_completed_jobs_dont_execute :
    completed_jobs_dont_execute inflated_job_cost
      (sched_new job_arrival job_cost arr_seq higher_eq_priority
        sched_susp inflated_job_cost j R) := by
  intro j0 t0
  induction t0 with
  | zero =>
    simp only [service, service_during, Finset.Ico_self, Finset.sum_empty]
    exact Nat.zero_le _
  | succ t0 ih =>
    simp only [service, service_during] at ih ⊢
    rw [Finset.sum_Ico_succ_top (Nat.zero_le t0)]
    set S := ∑ i ∈ Finset.Ico 0 t0, service_at (sched_new job_arrival job_cost arr_seq higher_eq_priority sched_susp inflated_job_cost j R) j0 i with hS_def
    -- Now ih : S ≤ inflated_job_cost j0
    -- Goal: S + service_at ... t0 ≤ inflated_job_cost j0
    by_cases hlt : S < inflated_job_cost j0
    · -- Case: service < inflated_job_cost, so adding at most 1 is still ≤
      have h1 := service_at_most_one (sched_new job_arrival job_cost arr_seq higher_eq_priority sched_susp inflated_job_cost j R) j0 t0
      omega
    · -- Case: service = inflated_job_cost (by ih + not less)
      push_neg at hlt
      have heq : S = inflated_job_cost j0 := by omega
      -- j0 is completed at t0, so not scheduled at t0
      -- Need to show service_at = 0 (i.e., j0 is not scheduled at t0)
      have hcomp : completed_by inflated_job_cost (sched_new job_arrival job_cost arr_seq higher_eq_priority sched_susp inflated_job_cost j R) j0 t0 := by
        simp only [completed_by, service, service_during]
        rw [← hS_def]; omega
      -- If scheduled, then it must be in the filter list, which requires pending (= not completed)
      -- So service_at must be 0
      suffices hsa : service_at (sched_new job_arrival job_cost arr_seq higher_eq_priority sched_susp inflated_job_cost j R) j0 t0 = 0 by omega
      simp only [service_at, scheduled_at]
      -- Need to show sched_new ... t0 ≠ some j0
      -- Unfold sched_new using construction function
      have USE := @sched_new_uses_construction_function Job _ job_arrival job_cost arr_seq
        H_arrival_times_are_consistent higher_eq_priority H_priority_is_reflexive
        H_priority_is_transitive H_priority_is_total sched_susp H_jobs_come_from_arrival_sequence
        job_suspension_duration H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
        H_work_conserving H_respects_priority H_respects_self_suspensions j R inflated_job_cost
        H_job_costs_do_not_decrease t0
      -- If sched_new t0 = some j0, then j0 is in the filter list → pending → not completed
      -- But j0 IS completed, contradiction
      cases hd : (sched_new job_arrival job_cost arr_seq higher_eq_priority sched_susp inflated_job_cost j R t0 == some j0) with
      | false => simp [Bool.toNat]
      | true =>
        exfalso
        rw [beq_iff_eq] at hd
        rw [USE] at hd
        simp only [build_schedule] at hd
        by_cases hLT : t0 < job_arrival j + R
        · simp only [hLT, ↓reduceIte] at hd
          have hIN := seq_min_in_seq (higher_eq_priority t0) _ j0 hd
          simp only [jobs_that_are_late_or_scheduled_in_sched_susp, List.mem_filter] at hIN
          have hPend := hIN.2
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hPend
          exact hPend.1.2 hcomp
        · simp only [hLT, ↓reduceIte] at hd
          have hIN := seq_min_in_seq (higher_eq_priority t0) _ j0 hd
          simp only [pending_jobs, List.mem_filter] at hIN
          simp only [decide_eq_true_eq] at hIN
          exact hIN.2.2 hcomp

end BasicScheduleProperties

section ServiceInvariant

variable (t : Time)
variable (H_before_R : t ≤ job_arrival j + R)

include H_arrival_times_are_consistent H_priority_is_reflexive H_priority_is_transitive H_priority_is_total H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_work_conserving H_respects_priority H_respects_self_suspensions H_job_costs_do_not_decrease H_before_R in
theorem sched_new_service_invariant :
    ∀ any_j,
      service (sched_new job_arrival job_cost arr_seq higher_eq_priority
        sched_susp inflated_job_cost j R) any_j t ≤
      service sched_susp any_j t + (inflated_job_cost any_j - job_cost any_j) := by
  -- Helper: service(t+1) = service(t) + service_at(t)
  have service_succ : ∀ (sc : schedule Job) (jj : Job) (tt : ℕ),
      service sc jj (tt + 1) = service sc jj tt + service_at sc jj tt := by
    intro sc jj tt
    simp only [service, service_during]
    rw [Finset.sum_Ico_succ_top (Nat.zero_le tt)]
  -- Induction on t
  revert H_before_R
  induction t with
  | zero =>
    intro _BEFORE j0
    simp only [service, service_during, Finset.Ico_self, Finset.sum_empty]
    exact Nat.zero_le _
  | succ t' ih =>
    intro BEFORE
    have BEFORE' : t' ≤ job_arrival j + R := Nat.le_of_succ_le BEFORE
    have ih' := ih BEFORE'
    intro j0
    -- Split service(t'+1) = service(t') + service_at(t')
    set sn := sched_new job_arrival job_cost arr_seq higher_eq_priority sched_susp inflated_job_cost j R
    by_cases SCHEDn : scheduled_at sn j0 t' = true
    · -- j0 IS scheduled at t' in sched_new
      -- Look at the construction function
      have hEQ : sn t' = some j0 := by
        simp only [scheduled_at] at SCHEDn; rwa [beq_iff_eq] at SCHEDn
      have USE := @sched_new_uses_construction_function Job _ job_arrival job_cost arr_seq
        H_arrival_times_are_consistent higher_eq_priority H_priority_is_reflexive
        H_priority_is_transitive H_priority_is_total sched_susp H_jobs_come_from_arrival_sequence
        job_suspension_duration H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
        H_work_conserving H_respects_priority H_respects_self_suspensions j R inflated_job_cost
        H_job_costs_do_not_decrease t'
      rw [show sn = sched_new job_arrival job_cost arr_seq higher_eq_priority sched_susp inflated_job_cost j R from rfl] at hEQ
      rw [USE] at hEQ
      simp only [build_schedule] at hEQ
      have hLT : t' < job_arrival j + R := Nat.lt_of_succ_le BEFORE
      simp only [hLT, ↓reduceIte] at hEQ
      have hIN := seq_min_in_seq (higher_eq_priority t') _ j0 hEQ
      simp only [jobs_that_are_late_or_scheduled_in_sched_susp, List.mem_filter] at hIN
      have hPend := hIN.2
      simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true] at hPend
      obtain ⟨⟨_, _⟩, hOR⟩ := hPend
      cases hOR with
      | inl hLate =>
        -- j0 is late: service_new(t') < service_susp(t') + (inflated_cost - cost)
        simp only [job_is_late, decide_eq_true_eq] at hLate
        -- Fold sn in hLate so omega can unify with goal
        change service sn j0 t' < service sched_susp j0 t' + (inflated_job_cost j0 - job_cost j0) at hLate
        -- service_new(t'+1) ≤ service_new(t') + 1
        rw [service_succ sn j0 t']
        have h1 := service_at_most_one sn j0 t'
        -- service_susp(t') ≤ service_susp(t'+1)
        rw [service_succ sched_susp j0 t']
        -- From hLate: sn_service(t') + 1 ≤ susp_service(t') + (inflated - cost)
        -- Goal: sn_service(t') + sn_service_at(t') ≤ (susp_service(t') + susp_service_at(t')) + (inflated - cost)
        -- Strategy: LHS ≤ sn_service(t') + 1 ≤ susp_service(t') + (inflated-cost) ≤ RHS
        apply Nat.le_trans
        · -- sn_service(t') + sn_service_at(t') ≤ sn_service(t') + 1
          exact Nat.add_le_add_left h1 _
        · -- sn_service(t') + 1 ≤ (susp_service(t') + susp_service_at(t')) + (inflated - cost)
          -- From hLate: sn_service(t') + 1 ≤ susp_service(t') + (inflated - cost)
          -- And: susp_service(t') ≤ susp_service(t') + susp_service_at(t')
          exact Nat.le_trans hLate (Nat.add_le_add_right (Nat.le_add_right _ _) _)
      | inr hSCHEDs =>
        -- j0 is scheduled in sched_susp at t'
        have hsa_susp : service_at sched_susp j0 t' = 1 := by
          simp only [service_at, scheduled_at] at hSCHEDs ⊢
          simp [hSCHEDs, Bool.toNat]
        have hsa_new : service_at sn j0 t' = 1 := by
          simp only [service_at, scheduled_at] at SCHEDn ⊢
          simp [SCHEDn, Bool.toNat]
        -- service(t'+1) = service(t') + 1 in both schedules
        rw [service_succ sn j0 t', service_succ sched_susp j0 t', hsa_susp, hsa_new]
        have := ih' j0
        omega
    · -- j0 is NOT scheduled at t' in sched_new
      have hsa_zero : service_at sn j0 t' = 0 := by
        simp only [service_at, scheduled_at] at SCHEDn ⊢
        cases hd : (sn t' == some j0) with
        | false => simp [Bool.toNat]
        | true => exfalso; exact SCHEDn hd
      -- service sn j0 (t'+1) = service sn j0 t'
      rw [service_succ sn j0 t', hsa_zero, Nat.add_zero]
      -- service sched_susp j0 t' ≤ service sched_susp j0 (t'+1)
      rw [service_succ sched_susp j0 t']
      have := ih' j0
      omega

include H_arrival_times_are_consistent H_priority_is_reflexive H_priority_is_transitive H_priority_is_total H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_work_conserving H_respects_priority H_respects_self_suspensions H_job_costs_do_not_decrease H_before_R in
theorem sched_new_jobs_complete_later :
    ∀ any_j,
      completed_by inflated_job_cost
        (sched_new job_arrival job_cost arr_seq higher_eq_priority
          sched_susp inflated_job_cost j R) any_j t →
      completed_by job_cost sched_susp any_j t := by
  intro j0 COMPn
  simp only [completed_by] at COMPn ⊢
  have hge := H_job_costs_do_not_decrease j0
  -- service_new ≤ service_susp + (inflated_cost - cost)
  -- inflated_cost ≤ service_new (from COMPn)
  -- so: inflated_cost ≤ service_susp + (inflated_cost - cost)
  -- i.e.: cost ≤ service_susp
  -- We need: job_cost j0 ≤ service sched_susp j0 t
  -- From COMPn: inflated_job_cost j0 ≤ service sn j0 t
  -- From INV: service sn j0 t ≤ service sched_susp j0 t + (inflated_job_cost j0 - job_cost j0)
  -- So: inflated_job_cost j0 ≤ service sched_susp j0 t + (inflated_job_cost j0 - job_cost j0)
  -- i.e.: job_cost j0 ≤ service sched_susp j0 t  (since inflated ≥ cost)
  have INV := @sched_new_service_invariant Job _ job_arrival job_cost arr_seq
    H_arrival_times_are_consistent higher_eq_priority H_priority_is_reflexive
    H_priority_is_transitive H_priority_is_total sched_susp H_jobs_come_from_arrival_sequence
    job_suspension_duration H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
    H_work_conserving H_respects_priority H_respects_self_suspensions j R inflated_job_cost
    H_job_costs_do_not_decrease t H_before_R j0
  -- inflated_job_cost j0 ≤ service_susp j0 t + (inflated_job_cost j0 - job_cost j0)
  have h1 : inflated_job_cost j0 ≤ service sched_susp j0 t + (inflated_job_cost j0 - job_cost j0) :=
    Nat.le_trans COMPn INV
  -- Since inflated ≥ cost, cost + (inflated - cost) = inflated ≤ service_susp + (inflated - cost)
  -- So cost ≤ service_susp
  have hcancel : job_cost j0 + (inflated_job_cost j0 - job_cost j0) = inflated_job_cost j0 :=
    Nat.add_sub_cancel' hge
  -- job_cost j0 + (inflated - cost) = inflated ≤ service_susp + (inflated - cost)
  have h2 : job_cost j0 + (inflated_job_cost j0 - job_cost j0) ≤
      service sched_susp j0 t + (inflated_job_cost j0 - job_cost j0) := by
    rw [hcancel]; exact h1
  exact Nat.le_of_add_le_add_right h2

end ServiceInvariant

section SuspensionPredicate

variable (any_j : Job)

include H_arrival_times_are_consistent H_priority_is_reflexive H_priority_is_transitive H_priority_is_total H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_work_conserving H_respects_priority H_respects_self_suspensions H_job_costs_do_not_decrease in
theorem suspended_in_sched_new_implies_arrived :
    ∀ t,
      suspended_in_sched_new job_arrival job_cost arr_seq higher_eq_priority
        sched_susp job_suspension_duration inflated_job_cost j R any_j t = true →
      has_arrived job_arrival any_j t := by
  intro t hsusp
  simp only [suspended_in_sched_new, Bool.and_eq_true, decide_eq_true_eq] at hsusp
  exact suspended_implies_arrived job_arrival job_cost job_suspension_duration sched_susp
    any_j t H_jobs_must_arrive_to_execute hsusp.1.2

include H_arrival_times_are_consistent H_priority_is_reflexive H_priority_is_transitive H_priority_is_total H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_work_conserving H_respects_priority H_respects_self_suspensions H_job_costs_do_not_decrease in
theorem suspended_in_sched_new_implies_not_completed :
    ∀ t,
      suspended_in_sched_new job_arrival job_cost arr_seq higher_eq_priority
        sched_susp job_suspension_duration inflated_job_cost j R any_j t = true →
      ¬ completed_by inflated_job_cost
        (sched_new job_arrival job_cost arr_seq higher_eq_priority
          sched_susp inflated_job_cost j R) any_j t := by
  intro t hsusp COMPn
  simp only [suspended_in_sched_new, Bool.and_eq_true, decide_eq_true_eq] at hsusp
  obtain ⟨⟨hLT, hSUSPs⟩, _⟩ := hsusp
  -- From suspended in sched_susp, we get ¬ completed_by job_cost sched_susp any_j t
  have hNotComp := suspended_implies_not_completed job_arrival job_cost job_suspension_duration sched_susp any_j t hSUSPs
  -- From completed in sched_new, we get completed in sched_susp (via sched_new_jobs_complete_later)
  have hComp := @sched_new_jobs_complete_later Job _ job_arrival job_cost arr_seq
    H_arrival_times_are_consistent higher_eq_priority H_priority_is_reflexive
    H_priority_is_transitive H_priority_is_total sched_susp H_jobs_come_from_arrival_sequence
    job_suspension_duration H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
    H_work_conserving H_respects_priority H_respects_self_suspensions j R inflated_job_cost
    H_job_costs_do_not_decrease t (Nat.le_of_lt hLT) any_j COMPn
  exact hNotComp hComp

include H_arrival_times_are_consistent H_priority_is_reflexive H_priority_is_transitive H_priority_is_total H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_work_conserving H_respects_priority H_respects_self_suspensions H_job_costs_do_not_decrease in
theorem executes_before_suspension_in_sched_new :
    ∀ t,
      t < job_arrival j + R →
      has_arrived job_arrival any_j t →
      ¬ (suspended_in_sched_new job_arrival job_cost arr_seq higher_eq_priority
          sched_susp job_suspension_duration inflated_job_cost j R any_j t = true) →
      suspended_in_sched_new job_arrival job_cost arr_seq higher_eq_priority
        sched_susp job_suspension_duration inflated_job_cost j R any_j (t + 1) = true →
      scheduled_at (sched_new job_arrival job_cost arr_seq higher_eq_priority
        sched_susp inflated_job_cost j R) any_j t = true := by
  intro t hLTr hARR hNOTSUSPn hSUSPn'
  set sn := sched_new job_arrival job_cost arr_seq higher_eq_priority sched_susp inflated_job_cost j R
  -- Parse suspended_in_sched_new at t+1
  simp only [suspended_in_sched_new, Bool.and_eq_true, decide_eq_true_eq] at hSUSPn'
  obtain ⟨⟨hLTr', hSUSPs'⟩, hNOTLATE'⟩ := hSUSPn'
  -- Parse ¬ suspended_in_sched_new at t
  -- suspended_in_sched_new = decide(t < arr_j+R) && decide(suspended_at ...) && !job_is_late
  -- hNOTSUSPn: ¬ (decide(t < ..) && decide(suspended ..) && !job_is_late = true)
  -- Since t < arr_j + R (from hLTr), the first decide is true.
  -- So this means: ¬ suspended_at OR job_is_late
  by_contra hNOTSCHEDn
  rw [Bool.not_eq_true] at hNOTSCHEDn
  by_cases hSUSPs : suspended_at job_arrival job_cost job_suspension_duration sched_susp any_j t
  · -- j IS suspended in sched_susp at t, so job_is_late must hold (from hNOTSUSPn)
    -- Since all three conditions hold except possibly !job_is_late,
    -- hNOTSUSPn tells us !job_is_late = false, i.e., job_is_late = true
    have hLATE : job_is_late job_cost sched_susp inflated_job_cost sn any_j t = true := by
      by_contra hNotLate
      rw [Bool.not_eq_true] at hNotLate
      apply hNOTSUSPn
      simp only [suspended_in_sched_new, Bool.and_eq_true, decide_eq_true_eq]
      refine ⟨⟨hLTr, hSUSPs⟩, ?_⟩
      change (!job_is_late job_cost sched_susp inflated_job_cost sn any_j t) = true
      simp [hNotLate]
    simp only [job_is_late, decide_eq_true_eq] at hLATE
    -- ¬ job_is_late at t+1 (from hNOTLATE')
    have hNOTLATE_prop : service sched_susp any_j (t + 1) + (inflated_job_cost any_j - job_cost any_j) ≤ service sn any_j (t + 1) := by
      change (!job_is_late job_cost sched_susp inflated_job_cost sn any_j (t + 1)) = true at hNOTLATE'
      simp only [job_is_late] at hNOTLATE'
      simp only [Bool.not_eq_true_eq_eq_false, decide_eq_false_iff_not] at hNOTLATE'
      omega
    -- service sn any_j (t+1) = service sn any_j t since not scheduled at t
    have hSAME : service sn any_j (t + 1) = service sn any_j t := by
      simp only [service, service_during]
      rw [Finset.sum_Ico_succ_top (Nat.zero_le t)]
      simp only [service_at, scheduled_at] at hNOTSCHEDn ⊢; simp [hNOTSCHEDn]
    have hMonoSusp : service sched_susp any_j t ≤ service sched_susp any_j (t + 1) := by
      simp only [service, service_during]
      rw [Finset.sum_Ico_succ_top (Nat.zero_le t)]
      exact Nat.le_add_right _ _
    omega
  · -- j is NOT suspended in sched_susp at t
    have hSAME : service sn any_j (t + 1) = service sn any_j t := by
      simp only [service, service_during]
      rw [Finset.sum_Ico_succ_top (Nat.zero_le t)]
      simp only [service_at, scheduled_at] at hNOTSCHEDn ⊢; simp [hNOTSCHEDn]
    have hNOTLATE_prop : service sched_susp any_j (t + 1) + (inflated_job_cost any_j - job_cost any_j) ≤ service sn any_j (t + 1) := by
      change (!job_is_late job_cost sched_susp inflated_job_cost sn any_j (t + 1)) = true at hNOTLATE'
      simp only [job_is_late] at hNOTLATE'
      simp only [Bool.not_eq_true_eq_eq_false, decide_eq_false_iff_not] at hNOTLATE'
      omega
    rw [hSAME] at hNOTLATE_prop
    have hINV := @sched_new_service_invariant Job _ job_arrival job_cost arr_seq
      H_arrival_times_are_consistent higher_eq_priority H_priority_is_reflexive
      H_priority_is_transitive H_priority_is_total sched_susp H_jobs_come_from_arrival_sequence
      job_suspension_duration H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
      H_work_conserving H_respects_priority H_respects_self_suspensions j R inflated_job_cost
      H_job_costs_do_not_decrease t (Nat.le_of_lt hLTr) any_j
    -- sched_susp must NOT schedule any_j at t
    have hNOTSCHEDs : ¬ (scheduled_at sched_susp any_j t = true) := by
      intro hSCHEDs
      have hsa_susp : service_at sched_susp any_j t = 1 := by
        simp only [service_at, scheduled_at] at hSCHEDs ⊢; simp [hSCHEDs, Bool.toNat]
      have : service sched_susp any_j (t + 1) = service sched_susp any_j t + 1 := by
        simp only [service, service_during]
        rw [Finset.sum_Ico_succ_top (Nat.zero_le t), hsa_susp]
      change service sn any_j t ≤ service sched_susp any_j t + (inflated_job_cost any_j - job_cost any_j) at hINV
      omega
    -- But j should be scheduled in sched_susp at t (by executes_before_suspension)
    exact absurd (@executes_before_suspension _ _ job_arrival job_cost job_suspension_duration sched_susp
        any_j t H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_respects_self_suspensions
        hARR hSUSPs hSUSPs') hNOTSCHEDs

include H_arrival_times_are_consistent H_priority_is_reflexive H_priority_is_transitive H_priority_is_total H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_work_conserving H_respects_priority H_respects_self_suspensions H_job_costs_do_not_decrease in
theorem suspended_in_sched_new_no_service_since_execution :
    ∀ t t_mid,
      suspended_in_sched_new job_arrival job_cost arr_seq higher_eq_priority
        sched_susp job_suspension_duration inflated_job_cost j R any_j t = true →
      time_after_last_execution job_arrival
        (sched_new job_arrival job_cost arr_seq higher_eq_priority
          sched_susp inflated_job_cost j R) any_j t ≤ t_mid ∧ t_mid < t →
      service (sched_new job_arrival job_cost arr_seq higher_eq_priority
        sched_susp inflated_job_cost j R) any_j t ≤
      service (sched_new job_arrival job_cost arr_seq higher_eq_priority
        sched_susp inflated_job_cost j R) any_j t_mid := by
  set sn := sched_new job_arrival job_cost arr_seq higher_eq_priority sched_susp inflated_job_cost j R
  have BEFORE := @executes_before_suspension_in_sched_new Job _ job_arrival job_cost arr_seq
    H_arrival_times_are_consistent higher_eq_priority H_priority_is_reflexive
    H_priority_is_transitive H_priority_is_total sched_susp H_jobs_come_from_arrival_sequence
    job_suspension_duration H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
    H_work_conserving H_respects_priority H_respects_self_suspensions j R inflated_job_cost
    H_job_costs_do_not_decrease any_j
  have sn_arrive := @sched_new_jobs_must_arrive_to_execute Job _ job_arrival job_cost arr_seq
    H_arrival_times_are_consistent higher_eq_priority H_priority_is_reflexive
    H_priority_is_transitive H_priority_is_total sched_susp H_jobs_come_from_arrival_sequence
    job_suspension_duration H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
    H_work_conserving H_respects_priority H_respects_self_suspensions j R inflated_job_cost
    H_job_costs_do_not_decrease
  intro t
  induction t with
  | zero => intro t_mid _ ⟨_, hlt⟩; exact absurd hlt (Nat.not_lt_zero t_mid)
  | succ t ih =>
    intro t_mid hSUSPn' ⟨hGE, hLT⟩
    simp only [Nat.succ_eq_add_one] at hGE hLT
    simp only [suspended_in_sched_new, Bool.and_eq_true, decide_eq_true_eq] at hSUSPn'
    obtain ⟨⟨hLTr', hSUSPs'⟩, hNOTLATE'⟩ := hSUSPn'
    have hLTr : t < job_arrival j + R := by simp only [Time] at *; omega
    have hARR : has_arrived job_arrival any_j (t + 1) :=
      suspended_implies_arrived job_arrival job_cost job_suspension_duration sched_susp any_j (t + 1) H_jobs_must_arrive_to_execute hSUSPs'
    by_cases hArrEq : job_arrival any_j = t + 1
    · simp only [service, service_during]
      rw [cumulative_service_before_job_arrival_zero job_arrival sn sn_arrive any_j 0 (t + 1) (by simp only [Time] at *; omega)]
      exact Nat.zero_le _
    · have hARR_t : has_arrived job_arrival any_j t := by
        unfold has_arrived at hARR ⊢; simp only [Time] at *; omega
      by_cases hSCHEDn : scheduled_at sn any_j t = true
      · -- j IS scheduled at t — suspension_start(t+1) ≥ t+1, contradicting t_mid < t+1
        exfalso
        have hTALE : time_after_last_execution job_arrival sn any_j (t + 1) ≥ t + 1 := by
          simp only [time_after_last_execution]
          have h_sb : scheduled_before sn any_j (t + 1) = true := by
            simp only [scheduled_before, decide_eq_true_eq]
            exact ⟨⟨t, by simp only [Time] at *; omega⟩, hSCHEDn⟩
          simp only [h_sb, ↓reduceIte, last_time_scheduled]
          have hne : max_nat_cond (fun t0 => scheduled_at sn any_j t0) 0 (t + 1) ≠ none :=
            max_nat_cond_exists _ _ _ t ⟨Nat.zero_le _, by simp only [Time] at *; omega⟩ hSCHEDn
          obtain ⟨m, hm⟩ : ∃ m, max_nat_cond (fun t0 => scheduled_at sn any_j t0) 0 (t + 1) = some m := by
            cases h : max_nat_cond (fun t0 => scheduled_at sn any_j t0) 0 (t + 1) with
            | some m => exact ⟨m, rfl⟩ | none => exact absurd h hne
          rw [hm]
          have hm_ge : m ≥ t :=
            max_nat_cond_computes_max _ _ _ _ hm t ⟨Nat.zero_le _, by simp only [Time] at *; omega⟩ hSCHEDn
          simp only [Time] at *; omega
        simp only [Time] at *; omega
      · -- j is NOT scheduled at t in sched_new
        have hServEq : service sn any_j (t + 1) = service sn any_j t := by
          simp only [service, service_during]
          rw [Finset.sum_Ico_succ_top (Nat.zero_le t)]
          simp only [service_at, scheduled_at] at hSCHEDn ⊢
          rw [Bool.not_eq_true] at hSCHEDn; simp [hSCHEDn]
        rw [hServEq]
        by_cases hEq : t_mid = t
        · subst hEq; exact le_refl _
        · have hLT' : t_mid < t := by simp only [Time] at *; omega
          have hSUSPn : suspended_in_sched_new job_arrival job_cost arr_seq higher_eq_priority
              sched_susp job_suspension_duration inflated_job_cost j R any_j t = true := by
            by_contra hNOTSUSPn
            have := BEFORE t hLTr hARR_t hNOTSUSPn
              (by simp only [suspended_in_sched_new, Bool.and_eq_true, decide_eq_true_eq]
                  exact ⟨⟨hLTr', hSUSPs'⟩, hNOTLATE'⟩)
            rw [Bool.not_eq_true] at hSCHEDn
            exact absurd this (by rw [hSCHEDn]; exact Bool.false_ne_true)
          apply ih t_mid hSUSPn
          constructor
          · exact Nat.le_trans
              (last_execution_monotonic job_arrival sn sn_arrive any_j t hARR_t (t + 1) (Nat.le_succ t))
              hGE
          · exact hLT'

include H_arrival_times_are_consistent H_priority_is_reflexive H_priority_is_transitive H_priority_is_total H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_work_conserving H_respects_priority H_respects_self_suspensions H_job_costs_do_not_decrease in
theorem suspended_in_sched_new_suspension_starts_no_earlier :
    ∀ t,
      has_arrived job_arrival any_j t →
      suspended_in_sched_new job_arrival job_cost arr_seq higher_eq_priority
        sched_susp job_suspension_duration inflated_job_cost j R any_j t = true →
      time_after_last_execution job_arrival sched_susp any_j t ≤
      time_after_last_execution job_arrival
        (sched_new job_arrival job_cost arr_seq higher_eq_priority
          sched_susp inflated_job_cost j R) any_j t := by
  set sn := sched_new job_arrival job_cost arr_seq higher_eq_priority sched_susp inflated_job_cost j R
  have BEFORE := @executes_before_suspension_in_sched_new Job _ job_arrival job_cost arr_seq
    H_arrival_times_are_consistent higher_eq_priority H_priority_is_reflexive
    H_priority_is_transitive H_priority_is_total sched_susp H_jobs_come_from_arrival_sequence
    job_suspension_duration H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
    H_work_conserving H_respects_priority H_respects_self_suspensions j R inflated_job_cost
    H_job_costs_do_not_decrease any_j
  have sn_arrive := @sched_new_jobs_must_arrive_to_execute Job _ job_arrival job_cost arr_seq
    H_arrival_times_are_consistent higher_eq_priority H_priority_is_reflexive
    H_priority_is_transitive H_priority_is_total sched_susp H_jobs_come_from_arrival_sequence
    job_suspension_duration H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
    H_work_conserving H_respects_priority H_respects_self_suspensions j R inflated_job_cost
    H_job_costs_do_not_decrease
  intro t
  induction t with
  | zero =>
    intro _hARR hSUSPn
    -- suspension_start sched_susp any_j 0 ≤ suspension_start sn any_j 0
    -- suspension_start at 0: scheduled_before ... 0 = false (no Fin 0)
    -- So time_after_last_execution = job_arrival any_j for both
    -- So it's job_arrival any_j ≤ job_arrival any_j
    simp only [time_after_last_execution]
    have h_sb_susp : scheduled_before sched_susp any_j 0 = false := by
      simp only [scheduled_before, decide_eq_false_iff_not, not_exists]
      intro ⟨x, hx⟩; exact absurd hx (Nat.not_lt_zero x)
    have h_sb_sn : scheduled_before sn any_j 0 = false := by
      simp only [scheduled_before, decide_eq_false_iff_not, not_exists]
      intro ⟨x, hx⟩; exact absurd hx (Nat.not_lt_zero x)
    simp only [h_sb_susp, h_sb_sn, Bool.false_eq_true, ↓reduceIte]; exact le_refl _
  | succ t ih =>
    intro hARR hSUSPn'
    simp only [Nat.succ_eq_add_one] at hARR
    simp only [suspended_in_sched_new, Bool.and_eq_true, decide_eq_true_eq] at hSUSPn'
    obtain ⟨⟨hLTr', hSUSPs'⟩, hNOTLATE'⟩ := hSUSPn'
    have hLTr : t < job_arrival j + R := by simp only [Time] at *; omega
    by_cases hArrEq : job_arrival any_j = t + 1
    · apply Nat.le_trans _ (last_execution_after_arrival job_arrival sn sn_arrive any_j (t + 1))
      simp only [time_after_last_execution]
      have h_sb_susp : scheduled_before sched_susp any_j (t + 1) = false := by
        simp only [scheduled_before, decide_eq_false_iff_not, not_exists]
        intro ⟨x, hx⟩ hsched
        have harr := H_jobs_must_arrive_to_execute any_j x hsched
        unfold has_arrived at harr; simp only [Time] at *; omega
      simp only [h_sb_susp, Bool.false_eq_true, ↓reduceIte]; exact le_refl _
    · have hARR_t : has_arrived job_arrival any_j t := by
        unfold has_arrived at hARR ⊢; simp only [Time] at *; omega
      by_cases hSUSPn : suspended_in_sched_new job_arrival job_cost arr_seq higher_eq_priority
          sched_susp job_suspension_duration inflated_job_cost j R any_j t = true
      · have hSUSPn_parsed : suspended_at job_arrival job_cost job_suspension_duration sched_susp any_j t := by
          simp only [suspended_in_sched_new, Bool.and_eq_true, decide_eq_true_eq] at hSUSPn
          exact hSUSPn.1.2
        have hNotSchedSupp : ¬ (scheduled_at sched_susp any_j t = true) := by
          intro hsched; exact H_respects_self_suspensions any_j t hsched hSUSPn_parsed
        have hServEqSupp : service sched_susp any_j (t + 1) = service sched_susp any_j t := by
          simp only [service, service_during]
          rw [Finset.sum_Ico_succ_top (Nat.zero_le t)]
          simp only [service_at, scheduled_at] at hNotSchedSupp ⊢
          rw [Bool.not_eq_true] at hNotSchedSupp; simp [hNotSchedSupp]
        have hSameLastSupp := same_service_implies_same_last_execution job_arrival sched_susp
          H_jobs_must_arrive_to_execute any_j (t + 1) t hServEqSupp
        rw [hSameLastSupp]
        apply Nat.le_trans (ih hARR_t hSUSPn)
        exact last_execution_monotonic job_arrival sn sn_arrive any_j t hARR_t (t + 1) (Nat.le_succ t)
      · have hSCHEDn : scheduled_at sn any_j t = true :=
          BEFORE t hLTr hARR_t hSUSPn
            (by simp only [suspended_in_sched_new, Bool.and_eq_true, decide_eq_true_eq]
                exact ⟨⟨hLTr', hSUSPs'⟩, hNOTLATE'⟩)
        have hTALEsusp_le : time_after_last_execution job_arrival sched_susp any_j (t + 1) ≤ t + 1 := by
          have := hSUSPs'.2.1; simp only [Nat.succ_eq_add_one] at this; exact this
        have hTALEsn_ge : time_after_last_execution job_arrival sn any_j (t + 1) ≥ t + 1 := by
          simp only [time_after_last_execution]
          have h_sb : scheduled_before sn any_j (t + 1) = true := by
            simp only [scheduled_before, decide_eq_true_eq]
            exact ⟨⟨t, by simp only [Time] at *; omega⟩, hSCHEDn⟩
          simp only [h_sb, ↓reduceIte, last_time_scheduled]
          have hne : max_nat_cond (fun t0 => scheduled_at sn any_j t0) 0 (t + 1) ≠ none :=
            max_nat_cond_exists _ _ _ t ⟨Nat.zero_le _, by simp only [Time] at *; omega⟩ hSCHEDn
          obtain ⟨m, hm⟩ : ∃ m, max_nat_cond (fun t0 => scheduled_at sn any_j t0) 0 (t + 1) = some m := by
            cases h : max_nat_cond (fun t0 => scheduled_at sn any_j t0) 0 (t + 1) with
            | some m => exact ⟨m, rfl⟩ | none => exact absurd h hne
          rw [hm]
          show m + 1 ≥ t + 1
          have hm_ge : t ≤ m :=
            max_nat_cond_computes_max _ _ _ _ hm t ⟨Nat.zero_le _, by simp only [Time] at *; omega⟩ hSCHEDn
          omega
        show time_after_last_execution job_arrival sched_susp any_j (t + 1) ≤ time_after_last_execution job_arrival sn any_j (t + 1)
        exact Nat.le_trans hTALEsusp_le hTALEsn_ge

include H_arrival_times_are_consistent H_priority_is_reflexive H_priority_is_transitive H_priority_is_total H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_work_conserving H_respects_priority H_respects_self_suspensions H_job_costs_do_not_decrease in
theorem suspended_in_sched_new_is_continuous :
    ∀ t t_mid,
      suspended_in_sched_new job_arrival job_cost arr_seq higher_eq_priority
        sched_susp job_suspension_duration inflated_job_cost j R any_j t = true →
      time_after_last_execution job_arrival
        (sched_new job_arrival job_cost arr_seq higher_eq_priority
          sched_susp inflated_job_cost j R) any_j t ≤ t_mid ∧ t_mid < t →
      suspended_in_sched_new job_arrival job_cost arr_seq higher_eq_priority
        sched_susp job_suspension_duration inflated_job_cost j R any_j t_mid = true := by
  set sn := sched_new job_arrival job_cost arr_seq higher_eq_priority sched_susp inflated_job_cost j R
  have NOSERV := @suspended_in_sched_new_no_service_since_execution Job _ job_arrival job_cost arr_seq
    H_arrival_times_are_consistent higher_eq_priority H_priority_is_reflexive
    H_priority_is_transitive H_priority_is_total sched_susp H_jobs_come_from_arrival_sequence
    job_suspension_duration H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
    H_work_conserving H_respects_priority H_respects_self_suspensions j R inflated_job_cost
    H_job_costs_do_not_decrease any_j
  have NOEARLIER := @suspended_in_sched_new_suspension_starts_no_earlier Job _ job_arrival job_cost arr_seq
    H_arrival_times_are_consistent higher_eq_priority H_priority_is_reflexive
    H_priority_is_transitive H_priority_is_total sched_susp H_jobs_come_from_arrival_sequence
    job_suspension_duration H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
    H_work_conserving H_respects_priority H_respects_self_suspensions j R inflated_job_cost
    H_job_costs_do_not_decrease any_j
  have sn_arrive := @sched_new_jobs_must_arrive_to_execute Job _ job_arrival job_cost arr_seq
    H_arrival_times_are_consistent higher_eq_priority H_priority_is_reflexive
    H_priority_is_transitive H_priority_is_total sched_susp H_jobs_come_from_arrival_sequence
    job_suspension_duration H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
    H_work_conserving H_respects_priority H_respects_self_suspensions j R inflated_job_cost
    H_job_costs_do_not_decrease
  intro t
  -- Strong induction on t_mid
  intro t_mid SUSPn ⟨GE, LT⟩
  -- Parse SUSPn
  simp only [suspended_in_sched_new, Bool.and_eq_true, decide_eq_true_eq] at SUSPn
  obtain ⟨⟨hLTr, hSUSPt⟩, hNOTLATEt⟩ := SUSPn
  -- Goal: suspended_in_sched_new ... any_j t_mid = true
  simp only [suspended_in_sched_new, Bool.and_eq_true, decide_eq_true_eq]
  -- Need: (t_mid < arr_j + R ∧ suspended_at ... any_j t_mid) ∧ ¬job_is_late at t_mid
  constructor
  · -- First part: t_mid < arr_j + R ∧ suspended_at ... any_j t_mid
    constructor
    · -- t_mid < arr_j + R
      exact Nat.lt_trans LT hLTr
    · -- suspended_at ... any_j t_mid
      -- Use suspended_in_suspension_interval with pivot t
      apply suspended_in_suspension_interval job_arrival job_cost job_suspension_duration sched_susp any_j t t_mid
        H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_respects_self_suspensions
      · -- has_arrived job_arrival any_j t
        exact suspended_implies_arrived job_arrival job_cost job_suspension_duration sched_susp any_j t
          H_jobs_must_arrive_to_execute hSUSPt
      · -- ¬ completed_by job_cost sched_susp any_j t_mid
        intro COMPmid
        have hNotComp := suspended_implies_not_completed job_arrival job_cost job_suspension_duration sched_susp any_j t hSUSPt
        exact hNotComp (completion_monotonic job_cost sched_susp any_j t_mid t (Nat.le_of_lt LT) COMPmid)
      · -- time_after_last_execution ... sched_susp any_j t ≤ t_mid ∧ t_mid < ... + suspension_duration
        constructor
        · -- time_after_last_execution sched_susp any_j t ≤ t_mid
          exact Nat.le_trans (NOEARLIER t (suspended_implies_arrived job_arrival job_cost job_suspension_duration sched_susp any_j t H_jobs_must_arrive_to_execute hSUSPt) (by simp only [suspended_in_sched_new, Bool.and_eq_true, decide_eq_true_eq]; exact ⟨⟨hLTr, hSUSPt⟩, hNOTLATEt⟩)) GE
        · -- t_mid < time_after_last_execution sched_susp any_j t + suspension_duration
          exact Nat.lt_trans LT hSUSPt.2.2
  · -- Second part: ¬ job_is_late at t_mid
    -- !job_is_late ... at t_mid
    -- job_is_late = decide (service sn any_j t_mid < service sched_susp any_j t_mid + (inflated - cost))
    -- ¬ job_is_late means: service sched_susp any_j t_mid + (inflated - cost) ≤ service sn any_j t_mid
    change (!job_is_late job_cost sched_susp inflated_job_cost sn any_j t_mid) = true
    simp only [job_is_late, Bool.not_eq_true_eq_eq_false, decide_eq_false_iff_not]
    -- Need: ¬ (service sn any_j t_mid < service sched_susp any_j t_mid + (inflated - cost))
    push_neg
    -- Need: service sched_susp any_j t_mid + (inflated - cost) ≤ service sn any_j t_mid
    -- From hNOTLATEt: ¬ job_is_late at t
    -- i.e., service sched_susp any_j t + (inflated - cost) ≤ service sn any_j t
    change (!job_is_late job_cost sched_susp inflated_job_cost sn any_j t) = true at hNOTLATEt
    simp only [job_is_late, Bool.not_eq_true_eq_eq_false, decide_eq_false_iff_not] at hNOTLATEt
    push_neg at hNOTLATEt
    -- hNOTLATEt: service sched_susp any_j t + (inflated - cost) ≤ service sn any_j t
    -- INV at t: service sn any_j t ≤ service sched_susp any_j t + (inflated - cost)
    have INV := @sched_new_service_invariant Job _ job_arrival job_cost arr_seq
      H_arrival_times_are_consistent higher_eq_priority H_priority_is_reflexive
      H_priority_is_transitive H_priority_is_total sched_susp H_jobs_come_from_arrival_sequence
      job_suspension_duration H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
      H_work_conserving H_respects_priority H_respects_self_suspensions j R inflated_job_cost
      H_job_costs_do_not_decrease t (Nat.le_of_lt hLTr) any_j
    -- So service sn any_j t = service sched_susp any_j t + (inflated - cost)
    change service sn any_j t ≤ service sched_susp any_j t + (inflated_job_cost any_j - job_cost any_j) at INV
    change service sched_susp any_j t + (inflated_job_cost any_j - job_cost any_j) ≤ service sn any_j t at hNOTLATEt
    have SAME : service sn any_j t = service sched_susp any_j t + (inflated_job_cost any_j - job_cost any_j) := by
      omega
    -- Also: service sn any_j t ≤ service sn any_j t_mid (via NOSERV)
    -- Reconstruct the original boolean form for NOSERV
    have hSUSPn_orig : suspended_in_sched_new job_arrival job_cost arr_seq higher_eq_priority
        sched_susp job_suspension_duration inflated_job_cost j R any_j t = true := by
      simp only [suspended_in_sched_new, Bool.and_eq_true, decide_eq_true_eq]
      refine ⟨⟨hLTr, hSUSPt⟩, ?_⟩
      change (!job_is_late job_cost sched_susp inflated_job_cost sn any_j t) = true
      simp only [job_is_late, Bool.not_eq_true_eq_eq_false, decide_eq_false_iff_not]
      omega
    have hNOSERV : service sn any_j t ≤ service sn any_j t_mid := by
      apply NOSERV t t_mid
      · exact hSUSPn_orig
      · exact ⟨GE, LT⟩
    -- service sched_susp any_j t_mid ≤ service sched_susp any_j t (since t_mid < t)
    have hMonoSusp : service sched_susp any_j t_mid ≤ service sched_susp any_j t := by
      simp only [service, service_during]
      apply Finset.sum_le_sum_of_subset
      intro x hx; rw [Finset.mem_Ico] at hx ⊢
      exact ⟨hx.1, Nat.lt_of_lt_of_le hx.2 (Nat.le_of_lt LT)⟩
    -- Combine: service sched_susp any_j t_mid + (inflated - cost) ≤ service sched_susp any_j t + (inflated - cost) = service sn any_j t ≤ service sn any_j t_mid
    calc service sched_susp any_j t_mid + (inflated_job_cost any_j - job_cost any_j)
        ≤ service sched_susp any_j t + (inflated_job_cost any_j - job_cost any_j) := Nat.add_le_add_right hMonoSusp _
      _ = service sn any_j t := SAME.symm
      _ ≤ service sn any_j t_mid := hNOSERV

end SuspensionPredicate

section SuspensionTable

include H_arrival_times_are_consistent H_priority_is_reflexive H_priority_is_transitive H_priority_is_total H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_work_conserving H_respects_priority H_respects_self_suspensions H_job_costs_do_not_decrease in
theorem suspended_in_sched_new_only_inside_window :
    ∀ any_j t,
      job_arrival j + R ≤ t →
      ¬ suspended_at job_arrival inflated_job_cost
          (reduced_suspension_duration job_arrival job_cost arr_seq higher_eq_priority
            sched_susp job_suspension_duration inflated_job_cost j R)
          (sched_new job_arrival job_cost arr_seq higher_eq_priority
            sched_susp inflated_job_cost j R) any_j t := by
  set sn := sched_new job_arrival job_cost arr_seq higher_eq_priority sched_susp inflated_job_cost j R
  set susp_new := suspended_in_sched_new job_arrival job_cost arr_seq higher_eq_priority sched_susp
    job_suspension_duration inflated_job_cost j R
  set red_susp := reduced_suspension_duration job_arrival job_cost arr_seq higher_eq_priority sched_susp
    job_suspension_duration inflated_job_cost j R
  have sn_arrive := @sched_new_jobs_must_arrive_to_execute Job _ job_arrival job_cost arr_seq
    H_arrival_times_are_consistent higher_eq_priority H_priority_is_reflexive
    H_priority_is_transitive H_priority_is_total sched_susp H_jobs_come_from_arrival_sequence
    job_suspension_duration H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
    H_work_conserving H_respects_priority H_respects_self_suspensions j R inflated_job_cost
    H_job_costs_do_not_decrease
  -- Key: show build_suspension_duration_local = build_suspension_duration for our purposes
  -- reduced_suspension_duration = build_suspension_duration_local sn (arr_j+R) susp_new
  -- We need: ∀ any_j s, red_susp any_j s = build_suspension_duration sn (job_arrival j + R) susp_new any_j s
  have susp_eq : ∀ j0 s, red_susp j0 s =
      build_suspension_duration sn (job_arrival j + R) susp_new j0 s := by
    intro j0 s
    show build_suspension_duration_local sn (job_arrival j + R) susp_new j0 s =
         build_suspension_duration sn (job_arrival j + R) susp_new j0 s
    simp only [build_suspension_duration_local, build_suspension_duration, Finset.range_eq_Ico]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro t' _
    by_cases hs : service sn j0 t' = s
    · simp [hs, Bool.toNat]
    · simp [hs, Bool.toNat]
  -- Now we can rephrase the goal in terms of build_suspension_duration
  intro any_j t hLE
  -- First, case on whether any_j has arrived
  by_cases hARR : has_arrived job_arrival any_j t
  · -- any_j has arrived
    -- Apply suspension_duration_no_suspension_after_t_max
    intro hSUSP
    -- Convert suspended_at with red_susp to suspended_at with build_suspension_duration
    have hSUSP' : suspended_at job_arrival inflated_job_cost
        (build_suspension_duration sn (job_arrival j + R) susp_new) sn any_j t := by
      obtain ⟨h1, h2, h3⟩ := hSUSP
      refine ⟨h1, h2, ?_⟩
      simp only [suspension_duration] at h3 ⊢
      rwa [← susp_eq]
    exact suspension_duration_no_suspension_after_t_max job_arrival
      inflated_job_cost sn sn_arrive (job_arrival j + R) susp_new
      (fun j0 t0 hLT hS => @suspended_in_sched_new_implies_arrived Job _ job_arrival job_cost arr_seq
        H_arrival_times_are_consistent higher_eq_priority H_priority_is_reflexive
        H_priority_is_transitive H_priority_is_total sched_susp H_jobs_come_from_arrival_sequence
        job_suspension_duration H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
        H_work_conserving H_respects_priority H_respects_self_suspensions j R inflated_job_cost
        H_job_costs_do_not_decrease j0 t0 hS)
      (fun j0 t0 hLT hS => @suspended_in_sched_new_implies_not_completed Job _ job_arrival job_cost arr_seq
        H_arrival_times_are_consistent higher_eq_priority H_priority_is_reflexive
        H_priority_is_transitive H_priority_is_total sched_susp H_jobs_come_from_arrival_sequence
        job_suspension_duration H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
        H_work_conserving H_respects_priority H_respects_self_suspensions j R inflated_job_cost
        H_job_costs_do_not_decrease j0 t0 hS)
      (fun j0 t0 t_susp hLT hS ⟨hge, hlt⟩ => @suspended_in_sched_new_is_continuous Job _ job_arrival job_cost arr_seq
        H_arrival_times_are_consistent higher_eq_priority H_priority_is_reflexive
        H_priority_is_transitive H_priority_is_total sched_susp H_jobs_come_from_arrival_sequence
        job_suspension_duration H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
        H_work_conserving H_respects_priority H_respects_self_suspensions j R inflated_job_cost
        H_job_costs_do_not_decrease j0 t0 t_susp hS ⟨hge, hlt⟩)
      any_j t hARR hLE hSUSP'
  · -- any_j has NOT arrived
    intro hSUSP
    exact hARR (suspended_implies_arrived job_arrival inflated_job_cost red_susp sn any_j t sn_arrive hSUSP)

include H_arrival_times_are_consistent H_priority_is_reflexive H_priority_is_transitive H_priority_is_total H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_work_conserving H_respects_priority H_respects_self_suspensions H_job_costs_do_not_decrease in
theorem sched_new_suspension_matches :
    ∀ any_j t,
      t < job_arrival j + R →
      (suspended_in_sched_new job_arrival job_cost arr_seq higher_eq_priority
        sched_susp job_suspension_duration inflated_job_cost j R any_j t = true ↔
      suspended_at job_arrival inflated_job_cost
        (reduced_suspension_duration job_arrival job_cost arr_seq higher_eq_priority
          sched_susp job_suspension_duration inflated_job_cost j R)
        (sched_new job_arrival job_cost arr_seq higher_eq_priority
          sched_susp inflated_job_cost j R) any_j t) := by
  set sn := sched_new job_arrival job_cost arr_seq higher_eq_priority sched_susp inflated_job_cost j R
  set susp_new := suspended_in_sched_new job_arrival job_cost arr_seq higher_eq_priority sched_susp
    job_suspension_duration inflated_job_cost j R
  set red_susp := reduced_suspension_duration job_arrival job_cost arr_seq higher_eq_priority sched_susp
    job_suspension_duration inflated_job_cost j R
  have sn_arrive := @sched_new_jobs_must_arrive_to_execute Job _ job_arrival job_cost arr_seq
    H_arrival_times_are_consistent higher_eq_priority H_priority_is_reflexive
    H_priority_is_transitive H_priority_is_total sched_susp H_jobs_come_from_arrival_sequence
    job_suspension_duration H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
    H_work_conserving H_respects_priority H_respects_self_suspensions j R inflated_job_cost
    H_job_costs_do_not_decrease
  have susp_eq : ∀ j0 s, red_susp j0 s =
      build_suspension_duration sn (job_arrival j + R) susp_new j0 s := by
    intro j0 s
    show build_suspension_duration_local sn (job_arrival j + R) susp_new j0 s =
         build_suspension_duration sn (job_arrival j + R) susp_new j0 s
    simp only [build_suspension_duration_local, build_suspension_duration, Finset.range_eq_Ico]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro t' _
    by_cases hs : service sn j0 t' = s
    · simp [hs, Bool.toNat]
    · simp [hs, Bool.toNat]
  intro any_j t hLT
  have h := suspension_duration_matches_predicate_up_to_t_max job_arrival inflated_job_cost
    sn sn_arrive (job_arrival j + R) susp_new
    (fun j0 t0 hLT' hS => @suspended_in_sched_new_implies_arrived Job _ job_arrival job_cost arr_seq
      H_arrival_times_are_consistent higher_eq_priority H_priority_is_reflexive
      H_priority_is_transitive H_priority_is_total sched_susp H_jobs_come_from_arrival_sequence
      job_suspension_duration H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
      H_work_conserving H_respects_priority H_respects_self_suspensions j R inflated_job_cost
      H_job_costs_do_not_decrease j0 t0 hS)
    (fun j0 t0 hLT' hS => @suspended_in_sched_new_implies_not_completed Job _ job_arrival job_cost arr_seq
      H_arrival_times_are_consistent higher_eq_priority H_priority_is_reflexive
      H_priority_is_transitive H_priority_is_total sched_susp H_jobs_come_from_arrival_sequence
      job_suspension_duration H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
      H_work_conserving H_respects_priority H_respects_self_suspensions j R inflated_job_cost
      H_job_costs_do_not_decrease j0 t0 hS)
    (fun j0 t0 t_susp hLT' hS ⟨hge, hlt⟩ => @suspended_in_sched_new_is_continuous Job _ job_arrival job_cost arr_seq
      H_arrival_times_are_consistent higher_eq_priority H_priority_is_reflexive
      H_priority_is_transitive H_priority_is_total sched_susp H_jobs_come_from_arrival_sequence
      job_suspension_duration H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
      H_work_conserving H_respects_priority H_respects_self_suspensions j R inflated_job_cost
      H_job_costs_do_not_decrease j0 t0 t_susp hS ⟨hge, hlt⟩)
    any_j t hLT
  -- h : susp_new any_j t = true ↔ suspended_at ... (build_suspension_duration sn (arr+R) susp_new) sn any_j t
  -- Goal: susp_new any_j t = true ↔ suspended_at ... red_susp sn any_j t
  -- Convert using susp_eq
  constructor
  · intro hSUSP
    obtain ⟨h1, h2, h3⟩ := h.mp hSUSP
    exact ⟨h1, h2, by simp only [suspension_duration] at h3 ⊢; rwa [susp_eq]⟩
  · intro hSUSP
    apply h.mpr
    obtain ⟨h1, h2, h3⟩ := hSUSP
    exact ⟨h1, h2, by simp only [suspension_duration] at h3 ⊢; rwa [← susp_eq]⟩

include H_arrival_times_are_consistent H_priority_is_reflexive H_priority_is_transitive H_priority_is_total H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_work_conserving H_respects_priority H_respects_self_suspensions H_job_costs_do_not_decrease in
theorem sched_new_has_shorter_suspension :
    ∀ any_j t,
      cumulative_suspension job_arrival inflated_job_cost
        (reduced_suspension_duration job_arrival job_cost arr_seq higher_eq_priority
          sched_susp job_suspension_duration inflated_job_cost j R)
        (sched_new job_arrival job_cost arr_seq higher_eq_priority
          sched_susp inflated_job_cost j R) any_j t ≤
      cumulative_suspension job_arrival job_cost job_suspension_duration
        sched_susp any_j t := by
  set sn := sched_new job_arrival job_cost arr_seq higher_eq_priority sched_susp inflated_job_cost j R
  set susp_new := suspended_in_sched_new job_arrival job_cost arr_seq higher_eq_priority sched_susp
    job_suspension_duration inflated_job_cost j R
  set red_susp := reduced_suspension_duration job_arrival job_cost arr_seq higher_eq_priority sched_susp
    job_suspension_duration inflated_job_cost j R
  have sn_arrive := @sched_new_jobs_must_arrive_to_execute Job _ job_arrival job_cost arr_seq
    H_arrival_times_are_consistent higher_eq_priority H_priority_is_reflexive
    H_priority_is_transitive H_priority_is_total sched_susp H_jobs_come_from_arrival_sequence
    job_suspension_duration H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
    H_work_conserving H_respects_priority H_respects_self_suspensions j R inflated_job_cost
    H_job_costs_do_not_decrease
  have MATCH := @sched_new_suspension_matches Job _ job_arrival job_cost arr_seq
    H_arrival_times_are_consistent higher_eq_priority H_priority_is_reflexive
    H_priority_is_transitive H_priority_is_total sched_susp H_jobs_come_from_arrival_sequence
    job_suspension_duration H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
    H_work_conserving H_respects_priority H_respects_self_suspensions j R inflated_job_cost
    H_job_costs_do_not_decrease
  have WINDOW := @suspended_in_sched_new_only_inside_window Job _ job_arrival job_cost arr_seq
    H_arrival_times_are_consistent higher_eq_priority H_priority_is_reflexive
    H_priority_is_transitive H_priority_is_total sched_susp H_jobs_come_from_arrival_sequence
    job_suspension_duration H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
    H_work_conserving H_respects_priority H_respects_self_suspensions j R inflated_job_cost
    H_job_costs_do_not_decrease
  intro j0 t
  -- cumulative_suspension = ∑ i ∈ Ico 0 t, if suspended_at ... then 1 else 0
  simp only [cumulative_suspension, cumulative_suspension_during]
  apply Finset.sum_le_sum
  intro i _
  -- For each i: need (if suspended_at ... red_susp sn j0 i then 1 else 0)
  --           ≤ (if suspended_at ... job_suspension_duration sched_susp j0 i then 1 else 0)
  by_cases hLTr : i < job_arrival j + R
  · -- Case i < arr_j + R: use MATCH
    have hM := (MATCH j0 i hLTr)
    by_cases hSuspNew : suspended_at job_arrival inflated_job_cost red_susp sn j0 i
    · -- suspended in sched_new
      -- By MATCH (backward), susp_new j0 i = true
      have hSN : susp_new j0 i = true := hM.mpr hSuspNew
      -- suspended_in_sched_new = (i < arr_j+R) && suspended_at_in_sched_susp && !job_is_late
      -- So suspended_at ... sched_susp j0 i
      simp only [susp_new, suspended_in_sched_new, Bool.and_eq_true, decide_eq_true_eq] at hSN
      have hSuspOld : suspended_at job_arrival job_cost job_suspension_duration sched_susp j0 i := hSN.1.2
      simp [hSuspNew, hSuspOld]
    · -- not suspended in sched_new
      simp [hSuspNew]
  · -- Case i ≥ arr_j + R
    push_neg at hLTr
    have hNotSusp : ¬ suspended_at job_arrival inflated_job_cost red_susp sn j0 i :=
      WINDOW j0 i hLTr
    simp [hNotSusp]

include H_arrival_times_are_consistent H_priority_is_reflexive H_priority_is_transitive H_priority_is_total H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_work_conserving H_respects_priority H_respects_self_suspensions H_job_costs_do_not_decrease in
theorem sched_new_has_shorter_total_suspension :
    ∀ any_j,
      total_suspension inflated_job_cost
        (reduced_suspension_duration job_arrival job_cost arr_seq higher_eq_priority
          sched_susp job_suspension_duration inflated_job_cost j R) any_j ≤
      total_suspension job_cost job_suspension_duration any_j := by
  intro any_j
  set sn := sched_new job_arrival job_cost arr_seq higher_eq_priority sched_susp inflated_job_cost j R
  set susp_new := suspended_in_sched_new job_arrival job_cost arr_seq higher_eq_priority sched_susp
    job_suspension_duration inflated_job_cost j R
  set red_susp := reduced_suspension_duration job_arrival job_cost arr_seq higher_eq_priority sched_susp
    job_suspension_duration inflated_job_cost j R
  have MATCH := @sched_new_suspension_matches Job _ job_arrival job_cost arr_seq
    H_arrival_times_are_consistent higher_eq_priority H_priority_is_reflexive
    H_priority_is_transitive H_priority_is_total sched_susp H_jobs_come_from_arrival_sequence
    job_suspension_duration H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
    H_work_conserving H_respects_priority H_respects_self_suspensions j R inflated_job_cost
    H_job_costs_do_not_decrease
  have SHORTER := @sched_new_has_shorter_suspension Job _ job_arrival job_cost arr_seq
    H_arrival_times_are_consistent higher_eq_priority H_priority_is_reflexive
    H_priority_is_transitive H_priority_is_total sched_susp H_jobs_come_from_arrival_sequence
    job_suspension_duration H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
    H_work_conserving H_respects_priority H_respects_self_suspensions j R inflated_job_cost
    H_job_costs_do_not_decrease
  -- Chain: total_susp(new) ≤ cumul(new, arr+R) ≤ cumul(old, arr+R) ≤ total_susp(old)
  have h_step1 : total_suspension inflated_job_cost red_susp any_j ≤
      cumulative_suspension job_arrival inflated_job_cost red_susp sn any_j (job_arrival j + R) := by
    simp only [total_suspension]
    have hred : ∀ s, red_susp any_j s =
        build_suspension_duration_local sn (job_arrival j + R) susp_new any_j s := fun s => rfl
    simp_rw [hred, build_suspension_duration_local]
    rw [Finset.sum_comm]
    simp only [cumulative_suspension, cumulative_suspension_during]
    rw [Finset.range_eq_Ico]
    apply Finset.sum_le_sum
    intro t' ht'
    rw [Finset.mem_Ico] at ht'
    have hLT' : t' < job_arrival j + R := ht'.2
    by_cases hS : susp_new any_j t' = true
    · -- susp_new = true → suspended_at holds
      have hSA : suspended_at job_arrival inflated_job_cost red_susp sn any_j t' :=
        (MATCH any_j t' hLT').mp hS
      have hNC := @suspended_in_sched_new_implies_not_completed Job _ job_arrival job_cost arr_seq
        H_arrival_times_are_consistent higher_eq_priority H_priority_is_reflexive
        H_priority_is_transitive H_priority_is_total sched_susp H_jobs_come_from_arrival_sequence
        job_suspension_duration H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
        H_work_conserving H_respects_priority H_respects_self_suspensions j R inflated_job_cost
        H_job_costs_do_not_decrease any_j t' hS
      have hServ : service sn any_j t' < inflated_job_cost any_j := by
        simp only [completed_by] at hNC; push_neg at hNC; exact hNC
      -- All simp steps: simplify RHS to 1
      simp only [hS, Bool.and_true, if_pos hSA]
      -- Remaining: ∑ x ∈ Ico 0 cost', if (decide(service=x)=true) then 1 else 0 ≤ 1
      -- Bound: sum = card of filter ≤ 1
      have h_card : ((Finset.Ico 0 (inflated_job_cost any_j)).filter
          (fun x => decide (service sn any_j t' = x) = true)).card ≤ 1 := by
        apply Finset.card_le_one.mpr
        intro a ha b hb
        simp only [Finset.mem_filter, decide_eq_true_eq] at ha hb
        exact ha.2.symm.trans hb.2
      calc ∑ x ∈ Finset.Ico 0 (inflated_job_cost any_j),
              (if (decide (service sn any_j t' = x) = true) then (1:ℕ) else 0)
          = ∑ _x ∈ (Finset.Ico 0 (inflated_job_cost any_j)).filter
              (fun x => decide (service sn any_j t' = x) = true), 1 :=
            (Finset.sum_filter _ (fun _ => 1)).symm
        _ = ((Finset.Ico 0 (inflated_job_cost any_j)).filter
              (fun x => decide (service sn any_j t' = x) = true)).card :=
            (Finset.card_eq_sum_ones _).symm
        _ ≤ 1 := h_card
    · -- susp_new = false
      rw [Bool.not_eq_true] at hS
      simp only [hS, Bool.and_false, Bool.false_eq_true, ↓reduceIte,
        Finset.sum_const_zero, Nat.zero_le]
  exact le_trans h_step1 (le_trans (SHORTER any_j (job_arrival j + R))
    (cumulative_suspension_le_total_suspension job_arrival job_cost job_suspension_duration sched_susp any_j
      H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_respects_self_suspensions
      0 (job_arrival j + R)))

end SuspensionTable

section AdditionalScheduleProperties

include H_arrival_times_are_consistent H_priority_is_reflexive H_priority_is_transitive H_priority_is_total H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_work_conserving H_respects_priority H_respects_self_suspensions H_job_costs_do_not_decrease in
theorem sched_new_respects_self_suspensions :
    respects_self_suspensions job_arrival inflated_job_cost
      (reduced_suspension_duration job_arrival job_cost arr_seq higher_eq_priority
        sched_susp job_suspension_duration inflated_job_cost j R)
      (sched_new job_arrival job_cost arr_seq higher_eq_priority
        sched_susp inflated_job_cost j R) := by
  set sn := sched_new job_arrival job_cost arr_seq higher_eq_priority sched_susp inflated_job_cost j R
  set red_susp := reduced_suspension_duration job_arrival job_cost arr_seq higher_eq_priority sched_susp
    job_suspension_duration inflated_job_cost j R
  set susp_new := suspended_in_sched_new job_arrival job_cost arr_seq higher_eq_priority sched_susp
    job_suspension_duration inflated_job_cost j R
  have MATCH := @sched_new_suspension_matches Job _ job_arrival job_cost arr_seq
    H_arrival_times_are_consistent higher_eq_priority H_priority_is_reflexive
    H_priority_is_transitive H_priority_is_total sched_susp H_jobs_come_from_arrival_sequence
    job_suspension_duration H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
    H_work_conserving H_respects_priority H_respects_self_suspensions j R inflated_job_cost
    H_job_costs_do_not_decrease
  have WINDOW := @suspended_in_sched_new_only_inside_window Job _ job_arrival job_cost arr_seq
    H_arrival_times_are_consistent higher_eq_priority H_priority_is_reflexive
    H_priority_is_transitive H_priority_is_total sched_susp H_jobs_come_from_arrival_sequence
    job_suspension_duration H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
    H_work_conserving H_respects_priority H_respects_self_suspensions j R inflated_job_cost
    H_job_costs_do_not_decrease
  have USE := @sched_new_uses_construction_function Job _ job_arrival job_cost arr_seq
    H_arrival_times_are_consistent higher_eq_priority H_priority_is_reflexive
    H_priority_is_transitive H_priority_is_total sched_susp H_jobs_come_from_arrival_sequence
    job_suspension_duration H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
    H_work_conserving H_respects_priority H_respects_self_suspensions j R inflated_job_cost
    H_job_costs_do_not_decrease
  -- respects_self_suspensions: ∀ j0 t, scheduled_at sn j0 t = true → ¬ suspended_at ... sn j0 t
  intro j0 t SCHEDn hSUSPn
  -- Case on t < arr_j + R vs t ≥ arr_j + R
  by_cases hLTr : t < job_arrival j + R
  · -- t < arr_j + R: use MATCH
    -- By MATCH, suspended_at red_susp sn j0 t ↔ susp_new j0 t = true
    have hSN : susp_new j0 t = true := (MATCH j0 t hLTr).mpr hSUSPn
    -- susp_new = decide(t < arr_j+R) && decide(suspended_at ... sched_susp j0 t) && !job_is_late
    simp only [susp_new, Prosa.Classic.Analysis.Uni.Susp.Sustainability.Allcosts.Reduction.SustainabilityAllCosts.suspended_in_sched_new, Bool.and_eq_true, decide_eq_true_eq] at hSN
    obtain ⟨⟨_, hSUSPs⟩, hNOTLATE⟩ := hSN
    -- j0 is suspended in sched_susp at t, so it's NOT scheduled in sched_susp at t
    -- (by H_respects_self_suspensions)
    -- j0 IS scheduled in sched_new at t. By the construction, it was picked from the late_or_sched filter list.
    -- So either job_is_late or scheduled_at sched_susp. But hNOTLATE says ¬ job_is_late.
    -- So scheduled_at sched_susp j0 t must be true. But that contradicts H_respects_self_suspensions.
    have hEQ : sn t = some j0 := by
      simp only [scheduled_at] at SCHEDn; rwa [beq_iff_eq] at SCHEDn
    have hEQ' : build_schedule job_arrival job_cost arr_seq higher_eq_priority sched_susp
        inflated_job_cost j R sn t = some j0 := by rw [← USE t]; exact hEQ
    simp only [build_schedule, hLTr, ↓reduceIte] at hEQ'
    have hIN := seq_min_in_seq (higher_eq_priority t) _ j0 hEQ'
    simp only [jobs_that_are_late_or_scheduled_in_sched_susp, List.mem_filter] at hIN
    have hFilt := hIN.2
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true] at hFilt
    obtain ⟨⟨_, _⟩, hOR⟩ := hFilt
    cases hOR with
    | inl hLate =>
      -- job_is_late contradicts hNOTLATE
      change (!Prosa.Classic.Analysis.Uni.Susp.Sustainability.Allcosts.Reduction.SustainabilityAllCosts.job_is_late job_cost sched_susp inflated_job_cost sn j0 t) = true at hNOTLATE
      simp only [Prosa.Classic.Analysis.Uni.Susp.Sustainability.Allcosts.Reduction.SustainabilityAllCosts.job_is_late, decide_eq_true_eq] at hLate
      simp only [Prosa.Classic.Analysis.Uni.Susp.Sustainability.Allcosts.Reduction.SustainabilityAllCosts.job_is_late, Bool.not_eq_true_eq_eq_false, decide_eq_false_iff_not] at hNOTLATE
      omega
    | inr hSCHEDs =>
      -- scheduled_at sched_susp j0 t contradicts H_respects_self_suspensions
      exact H_respects_self_suspensions j0 t hSCHEDs hSUSPs
  · -- t ≥ arr_j + R: no suspension at all after window
    push_neg at hLTr
    exact WINDOW j0 t hLTr hSUSPn

include H_arrival_times_are_consistent H_priority_is_reflexive H_priority_is_transitive H_priority_is_total H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_work_conserving H_respects_priority H_respects_self_suspensions H_job_costs_do_not_decrease in
theorem sched_new_work_conserving :
    work_conserving job_arrival inflated_job_cost
      (reduced_suspension_duration job_arrival job_cost arr_seq higher_eq_priority
        sched_susp job_suspension_duration inflated_job_cost j R)
      arr_seq
      (sched_new job_arrival job_cost arr_seq higher_eq_priority
        sched_susp inflated_job_cost j R) := by
  set sn := sched_new job_arrival job_cost arr_seq higher_eq_priority sched_susp inflated_job_cost j R
  set red_susp := reduced_suspension_duration job_arrival job_cost arr_seq higher_eq_priority sched_susp
    job_suspension_duration inflated_job_cost j R
  set susp_new := suspended_in_sched_new job_arrival job_cost arr_seq higher_eq_priority sched_susp
    job_suspension_duration inflated_job_cost j R
  have MATCH := @sched_new_suspension_matches Job _ job_arrival job_cost arr_seq
    H_arrival_times_are_consistent higher_eq_priority H_priority_is_reflexive
    H_priority_is_transitive H_priority_is_total sched_susp H_jobs_come_from_arrival_sequence
    job_suspension_duration H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
    H_work_conserving H_respects_priority H_respects_self_suspensions j R inflated_job_cost
    H_job_costs_do_not_decrease
  have WINDOW := @suspended_in_sched_new_only_inside_window Job _ job_arrival job_cost arr_seq
    H_arrival_times_are_consistent higher_eq_priority H_priority_is_reflexive
    H_priority_is_transitive H_priority_is_total sched_susp H_jobs_come_from_arrival_sequence
    job_suspension_duration H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
    H_work_conserving H_respects_priority H_respects_self_suspensions j R inflated_job_cost
    H_job_costs_do_not_decrease
  have USE := @sched_new_uses_construction_function Job _ job_arrival job_cost arr_seq
    H_arrival_times_are_consistent higher_eq_priority H_priority_is_reflexive
    H_priority_is_transitive H_priority_is_total sched_susp H_jobs_come_from_arrival_sequence
    job_suspension_duration H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
    H_work_conserving H_respects_priority H_respects_self_suspensions j R inflated_job_cost
    H_job_costs_do_not_decrease
  -- work_conserving: ∀ j0 t, arrives_in arr_seq j0 → backlogged ... j0 t → ∃ j_other, scheduled_at sn j_other t = true
  intro j0 t IN BACK
  obtain ⟨PEND, NOTSCHED, NOTSUSP⟩ := BACK
  have hUSE := USE t
  by_cases hLT : t < job_arrival j + R
  · -- PREFIX case
    cases h_bs : build_schedule job_arrival job_cost arr_seq higher_eq_priority sched_susp
        inflated_job_cost j R sn t with
    | some j_hp => exact ⟨j_hp, beq_iff_eq.mpr (hUSE.trans h_bs)⟩
    | none =>
      exfalso
      simp only [build_schedule, hLT, ↓reduceIte] at h_bs
      -- h_bs : seq_min (higher_eq_priority t) (jobs_that_are_late_or_scheduled_in_sched_susp ...) = none
      -- j0 is not scheduled in sn
      have hNOTSN : ¬ (scheduled_at sn j0 t = true) := NOTSCHED
      -- j0 is not suspended in the new schedule
      have hNOTSUSPn : ¬ suspended_at job_arrival inflated_job_cost red_susp sn j0 t := NOTSUSP
      -- From ¬ susp_new, either ¬ suspended_old or job_is_late
      have hORcases : ¬ suspended_at job_arrival job_cost job_suspension_duration sched_susp j0 t ∨
          Prosa.Classic.Analysis.Uni.Susp.Sustainability.Allcosts.Reduction.SustainabilityAllCosts.job_is_late
            job_cost sched_susp inflated_job_cost sn j0 t = true := by
        by_contra hContra
        push_neg at hContra
        obtain ⟨hSUSP_old, hNOT_late⟩ := hContra
        apply hNOTSUSPn
        rw [← MATCH j0 t hLT]
        simp only [susp_new, Prosa.Classic.Analysis.Uni.Susp.Sustainability.Allcosts.Reduction.SustainabilityAllCosts.suspended_in_sched_new, decide_eq_true hLT, decide_eq_true hSUSP_old, Bool.true_and]
        exact match hv : Prosa.Classic.Analysis.Uni.Susp.Sustainability.Allcosts.Reduction.SustainabilityAllCosts.job_is_late job_cost sched_susp inflated_job_cost sn j0 t with
        | false => rfl
        | true => absurd hv hNOT_late
      have ARR := PEND.1
      have NOTCOMPn := PEND.2
      have IN0 := arrived_between_implies_in_arrivals job_arrival arr_seq
        H_arrival_times_are_consistent j0 0 (t + 1) IN ⟨Nat.zero_le _, Nat.lt_succ_of_le ARR⟩
      rcases hORcases with hNOTSUSP_old | hLate
      · -- ¬ suspended in sched_susp
        by_cases hCOMP_old : completed_by job_cost sched_susp j0 t
        · -- completed in sched_susp → late
          have hLate : Prosa.Classic.Analysis.Uni.Susp.Sustainability.Allcosts.Reduction.SustainabilityAllCosts.job_is_late
              job_cost sched_susp inflated_job_cost sn j0 t = true := by
            simp only [Prosa.Classic.Analysis.Uni.Susp.Sustainability.Allcosts.Reduction.SustainabilityAllCosts.job_is_late, decide_eq_true_eq]
            simp only [completed_by] at hCOMP_old NOTCOMPn
            push_neg at NOTCOMPn
            have hge := H_job_costs_do_not_decrease j0
            exact calc service sn j0 t
                < inflated_job_cost j0 := NOTCOMPn
              _ = job_cost j0 + (inflated_job_cost j0 - job_cost j0) := (Nat.add_sub_cancel' hge).symm
              _ ≤ service sched_susp j0 t + (inflated_job_cost j0 - job_cost j0) := Nat.add_le_add_right hCOMP_old _
          -- j0 is late, pending, in arrivals → in filter list → seq_min_exists contradiction
          have h_mem : j0 ∈ jobs_that_are_late_or_scheduled_in_sched_susp job_arrival job_cost arr_seq
              sched_susp inflated_job_cost sn t := by
            simp only [jobs_that_are_late_or_scheduled_in_sched_susp, List.mem_filter]
            refine ⟨IN0, ?_⟩
            simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true]
            exact ⟨⟨ARR, NOTCOMPn⟩, Or.inl hLate⟩
          exact absurd h_bs (seq_min_exists (higher_eq_priority t) _ j0 h_mem)
        · -- not completed in sched_susp → backlogged in sched_susp
          -- j0 is arrived (ARR), not completed old (hCOMP_old), not suspended old, not scheduled
          -- Check if j0 is scheduled in sched_susp
          by_cases hSCHED_old : scheduled_at sched_susp j0 t = true
          · -- scheduled in sched_susp → in filter → seq_min_exists contradiction
            have h_mem : j0 ∈ jobs_that_are_late_or_scheduled_in_sched_susp job_arrival job_cost arr_seq
                sched_susp inflated_job_cost sn t := by
              simp only [jobs_that_are_late_or_scheduled_in_sched_susp, List.mem_filter]
              refine ⟨IN0, ?_⟩
              simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true]
              exact ⟨⟨ARR, NOTCOMPn⟩, Or.inr hSCHED_old⟩
            exact absurd h_bs (seq_min_exists (higher_eq_priority t) _ j0 h_mem)
          · -- backlogged in sched_susp → H_work_conserving gives j_hp scheduled in sched_susp
            have hBACK_old : Prosa.Classic.Model.Schedule.Uni.Susp.Schedule.backlogged
                job_arrival job_cost job_suspension_duration sched_susp j0 t :=
              ⟨⟨ARR, hCOMP_old⟩, hSCHED_old, hNOTSUSP_old⟩
            obtain ⟨j_hp, hSCHED_hp⟩ := H_work_conserving j0 t IN hBACK_old
            -- j_hp is scheduled in sched_susp → pending in sn?
            -- j_hp is scheduled in sched_susp → arrives_in
            have hIN_hp := H_jobs_come_from_arrival_sequence j_hp t hSCHED_hp
            -- If j_hp is completed in sn, then completed in sched_susp (via complete_later)
            -- But completed in sched_susp → not scheduled in sched_susp. Contradiction.
            by_cases hCOMP_hp_n : completed_by inflated_job_cost sn j_hp t
            · have hCOMP_hp_old := @sched_new_jobs_complete_later Job _ job_arrival job_cost arr_seq
                H_arrival_times_are_consistent higher_eq_priority H_priority_is_reflexive
                H_priority_is_transitive H_priority_is_total sched_susp H_jobs_come_from_arrival_sequence
                job_suspension_duration H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
                H_work_conserving H_respects_priority H_respects_self_suspensions j R inflated_job_cost
                H_job_costs_do_not_decrease t (Nat.le_of_lt hLT) j_hp hCOMP_hp_n
              exact absurd hSCHED_hp (completed_implies_not_scheduled job_cost sched_susp j_hp H_completed_jobs_dont_execute t hCOMP_hp_old)
            · -- j_hp not completed in sn, scheduled in sched_susp → in filter
              have hARR_hp := H_jobs_must_arrive_to_execute j_hp t hSCHED_hp
              have IN0_hp := arrived_between_implies_in_arrivals job_arrival arr_seq
                H_arrival_times_are_consistent j_hp 0 (t + 1) hIN_hp ⟨Nat.zero_le _, Nat.lt_succ_of_le hARR_hp⟩
              have h_mem : j_hp ∈ jobs_that_are_late_or_scheduled_in_sched_susp job_arrival job_cost arr_seq
                  sched_susp inflated_job_cost sn t := by
                simp only [jobs_that_are_late_or_scheduled_in_sched_susp, List.mem_filter]
                refine ⟨IN0_hp, ?_⟩
                simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true]
                exact ⟨⟨hARR_hp, hCOMP_hp_n⟩, Or.inr hSCHED_hp⟩
              exact absurd h_bs (seq_min_exists (higher_eq_priority t) _ j_hp h_mem)
      · -- job_is_late → in filter → seq_min_exists contradiction
        have h_mem : j0 ∈ jobs_that_are_late_or_scheduled_in_sched_susp job_arrival job_cost arr_seq
            sched_susp inflated_job_cost sn t := by
          simp only [jobs_that_are_late_or_scheduled_in_sched_susp, List.mem_filter]
          refine ⟨IN0, ?_⟩
          simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true]
          exact ⟨⟨ARR, NOTCOMPn⟩, Or.inl hLate⟩
        exact absurd h_bs (seq_min_exists (higher_eq_priority t) _ j0 h_mem)
  · -- SUFFIX case
    push_neg at hLT
    cases h_bs : build_schedule job_arrival job_cost arr_seq higher_eq_priority sched_susp
        inflated_job_cost j R sn t with
    | some j_hp => exact ⟨j_hp, beq_iff_eq.mpr (hUSE.trans h_bs)⟩
    | none =>
      exfalso
      simp only [build_schedule, not_lt.mpr hLT, ↓reduceIte] at h_bs
      -- h_bs : seq_min ... (pending_jobs ...) = none
      have ARRs := PEND.1
      have NOTCOMPns := PEND.2
      have IN0 := arrived_between_implies_in_arrivals job_arrival arr_seq
        H_arrival_times_are_consistent j0 0 (t + 1) IN ⟨Nat.zero_le _, Nat.lt_succ_of_le ARRs⟩
      have h_mem : j0 ∈ Prosa.Classic.Analysis.Uni.Susp.Sustainability.Allcosts.Reduction.SustainabilityAllCosts.pending_jobs
          job_arrival arr_seq inflated_job_cost sn t := by
        simp only [Prosa.Classic.Analysis.Uni.Susp.Sustainability.Allcosts.Reduction.SustainabilityAllCosts.pending_jobs, List.mem_filter]
        exact ⟨IN0, by simp only [decide_eq_true_eq]; exact PEND⟩
      exact absurd h_bs (seq_min_exists (higher_eq_priority t) _ j0 h_mem)

include H_arrival_times_are_consistent H_priority_is_reflexive H_priority_is_transitive H_priority_is_total H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_work_conserving H_respects_priority H_respects_self_suspensions H_job_costs_do_not_decrease in
theorem sched_new_respects_policy :
    respects_JLDP_policy job_arrival inflated_job_cost
      (reduced_suspension_duration job_arrival job_cost arr_seq higher_eq_priority
        sched_susp job_suspension_duration inflated_job_cost j R)
      arr_seq
      (sched_new job_arrival job_cost arr_seq higher_eq_priority
        sched_susp inflated_job_cost j R)
      higher_eq_priority := by
  set sn := sched_new job_arrival job_cost arr_seq higher_eq_priority sched_susp inflated_job_cost j R
  set red_susp := reduced_suspension_duration job_arrival job_cost arr_seq higher_eq_priority sched_susp
    job_suspension_duration inflated_job_cost j R
  set susp_new := suspended_in_sched_new job_arrival job_cost arr_seq higher_eq_priority sched_susp
    job_suspension_duration inflated_job_cost j R
  have MATCH := @sched_new_suspension_matches Job _ job_arrival job_cost arr_seq
    H_arrival_times_are_consistent higher_eq_priority H_priority_is_reflexive
    H_priority_is_transitive H_priority_is_total sched_susp H_jobs_come_from_arrival_sequence
    job_suspension_duration H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
    H_work_conserving H_respects_priority H_respects_self_suspensions j R inflated_job_cost
    H_job_costs_do_not_decrease
  have WINDOW := @suspended_in_sched_new_only_inside_window Job _ job_arrival job_cost arr_seq
    H_arrival_times_are_consistent higher_eq_priority H_priority_is_reflexive
    H_priority_is_transitive H_priority_is_total sched_susp H_jobs_come_from_arrival_sequence
    job_suspension_duration H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
    H_work_conserving H_respects_priority H_respects_self_suspensions j R inflated_job_cost
    H_job_costs_do_not_decrease
  have USE := @sched_new_uses_construction_function Job _ job_arrival job_cost arr_seq
    H_arrival_times_are_consistent higher_eq_priority H_priority_is_reflexive
    H_priority_is_transitive H_priority_is_total sched_susp H_jobs_come_from_arrival_sequence
    job_suspension_duration H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
    H_work_conserving H_respects_priority H_respects_self_suspensions j R inflated_job_cost
    H_job_costs_do_not_decrease
  -- respects_JLDP_policy: ∀ j1 j2 t, arrives_in j1 → backlogged j1 t → scheduled_at sn j2 t → priority t j2 j1
  intro j1 j2 t ARRin BACK SCHED
  obtain ⟨⟨ARR1, NOTCOMPn1⟩, NOTSCHED, NOTSUSPn⟩ := BACK
  have hEQ2 : sn t = some j2 := by
    simp only [scheduled_at] at SCHED; rwa [beq_iff_eq] at SCHED
  have hUSE := USE t
  have hBS : build_schedule job_arrival job_cost arr_seq higher_eq_priority sched_susp
      inflated_job_cost j R sn t = some j2 := by rw [← hUSE]; exact hEQ2
  have IN1 := arrived_between_implies_in_arrivals job_arrival arr_seq
    H_arrival_times_are_consistent j1 0 (t + 1) ARRin ⟨Nat.zero_le _, Nat.lt_succ_of_le ARR1⟩
  by_cases hLT : t < job_arrival j + R
  · -- PREFIX case
    simp only [build_schedule, hLT, ↓reduceIte] at hBS
    -- hBS : seq_min (higher_eq_priority t) (jobs_that_are_late_or_scheduled_in_sched_susp ...) = some j2
    have hNOTSUSPn : ¬ suspended_at job_arrival inflated_job_cost red_susp sn j1 t := NOTSUSPn
    have hORcases : ¬ suspended_at job_arrival job_cost job_suspension_duration sched_susp j1 t ∨
        Prosa.Classic.Analysis.Uni.Susp.Sustainability.Allcosts.Reduction.SustainabilityAllCosts.job_is_late
          job_cost sched_susp inflated_job_cost sn j1 t = true := by
      by_contra hContra
      push_neg at hContra
      obtain ⟨hSUSP_old, hNOT_late⟩ := hContra
      apply hNOTSUSPn
      rw [← MATCH j1 t hLT]
      simp only [susp_new, Prosa.Classic.Analysis.Uni.Susp.Sustainability.Allcosts.Reduction.SustainabilityAllCosts.suspended_in_sched_new, decide_eq_true hLT, decide_eq_true hSUSP_old, Bool.true_and]
      exact match hv : Prosa.Classic.Analysis.Uni.Susp.Sustainability.Allcosts.Reduction.SustainabilityAllCosts.job_is_late job_cost sched_susp inflated_job_cost sn j1 t with
      | false => rfl
      | true => absurd hv hNOT_late
    -- Totality helper for the filter list
    have hTOT_prefix : ∀ x y : Job,
        x ∈ jobs_that_are_late_or_scheduled_in_sched_susp job_arrival job_cost arr_seq
          sched_susp inflated_job_cost sn t →
        y ∈ jobs_that_are_late_or_scheduled_in_sched_susp job_arrival job_cost arr_seq
          sched_susp inflated_job_cost sn t →
        higher_eq_priority t x y = true ∨ higher_eq_priority t y x = true := by
      intro x y hx hy
      simp only [jobs_that_are_late_or_scheduled_in_sched_susp, List.mem_filter] at hx hy
      exact H_priority_is_total x y t
        (in_arrivals_implies_arrived job_arrival arr_seq H_arrival_times_are_consistent x 0 (t + 1) hx.1)
        (in_arrivals_implies_arrived job_arrival arr_seq H_arrival_times_are_consistent y 0 (t + 1) hy.1)
    rcases hORcases with hNOTSUSP_old | hLate
    · -- ¬ suspended old
      by_cases hCOMP_old : completed_by job_cost sched_susp j1 t
      · -- completed in sched_susp → late
        have hLate : Prosa.Classic.Analysis.Uni.Susp.Sustainability.Allcosts.Reduction.SustainabilityAllCosts.job_is_late
            job_cost sched_susp inflated_job_cost sn j1 t = true := by
          simp only [Prosa.Classic.Analysis.Uni.Susp.Sustainability.Allcosts.Reduction.SustainabilityAllCosts.job_is_late, decide_eq_true_eq]
          simp only [completed_by] at hCOMP_old NOTCOMPn1
          push_neg at NOTCOMPn1
          have hge := H_job_costs_do_not_decrease j1
          exact calc service sn j1 t
              < inflated_job_cost j1 := NOTCOMPn1
            _ = job_cost j1 + (inflated_job_cost j1 - job_cost j1) := (Nat.add_sub_cancel' hge).symm
            _ ≤ service sched_susp j1 t + (inflated_job_cost j1 - job_cost j1) := Nat.add_le_add_right hCOMP_old _
        have h_mem : j1 ∈ jobs_that_are_late_or_scheduled_in_sched_susp job_arrival job_cost arr_seq
            sched_susp inflated_job_cost sn t := by
          simp only [jobs_that_are_late_or_scheduled_in_sched_susp, List.mem_filter]
          refine ⟨IN1, ?_⟩
          simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true]
          exact ⟨⟨ARR1, NOTCOMPn1⟩, Or.inl hLate⟩
        exact seq_min_computes_min (higher_eq_priority t) (fun x y z => H_priority_is_transitive t y x z)
          _ hTOT_prefix j2 j1 hBS h_mem
      · -- not completed in sched_susp
        by_cases hSCHED_old : scheduled_at sched_susp j1 t = true
        · -- scheduled in sched_susp → in filter → seq_min_computes_min
          have h_mem : j1 ∈ jobs_that_are_late_or_scheduled_in_sched_susp job_arrival job_cost arr_seq
              sched_susp inflated_job_cost sn t := by
            simp only [jobs_that_are_late_or_scheduled_in_sched_susp, List.mem_filter]
            refine ⟨IN1, ?_⟩
            simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true]
            exact ⟨⟨ARR1, NOTCOMPn1⟩, Or.inr hSCHED_old⟩
          exact seq_min_computes_min (higher_eq_priority t) (fun x y z => H_priority_is_transitive t y x z)
            _ hTOT_prefix j2 j1 hBS h_mem
        · -- backlogged in sched_susp → H_respects_priority gives transitivity
          have hBACK_old : Prosa.Classic.Model.Schedule.Uni.Susp.Schedule.backlogged
              job_arrival job_cost job_suspension_duration sched_susp j1 t :=
            ⟨⟨ARR1, hCOMP_old⟩, hSCHED_old, hNOTSUSP_old⟩
          obtain ⟨j_hp, hSCHED_hp⟩ := H_work_conserving j1 t ARRin hBACK_old
          have HIGHER := H_respects_priority j1 j_hp t ARRin hBACK_old hSCHED_hp
          -- j_hp is scheduled in sched_susp → arrives_in
          have hIN_hp := H_jobs_come_from_arrival_sequence j_hp t hSCHED_hp
          by_cases hCOMP_hp_n : completed_by inflated_job_cost sn j_hp t
          · have hCOMP_hp_old := @sched_new_jobs_complete_later Job _ job_arrival job_cost arr_seq
              H_arrival_times_are_consistent higher_eq_priority H_priority_is_reflexive
              H_priority_is_transitive H_priority_is_total sched_susp H_jobs_come_from_arrival_sequence
              job_suspension_duration H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
              H_work_conserving H_respects_priority H_respects_self_suspensions j R inflated_job_cost
              H_job_costs_do_not_decrease t (Nat.le_of_lt hLT) j_hp hCOMP_hp_n
            exact absurd hSCHED_hp (completed_implies_not_scheduled job_cost sched_susp j_hp H_completed_jobs_dont_execute t hCOMP_hp_old)
          · -- j_hp not completed in sn, scheduled in sched_susp → in filter
            have hARR_hp := H_jobs_must_arrive_to_execute j_hp t hSCHED_hp
            have IN0_hp := arrived_between_implies_in_arrivals job_arrival arr_seq
              H_arrival_times_are_consistent j_hp 0 (t + 1) hIN_hp ⟨Nat.zero_le _, Nat.lt_succ_of_le hARR_hp⟩
            have h_mem_hp : j_hp ∈ jobs_that_are_late_or_scheduled_in_sched_susp job_arrival job_cost arr_seq
                sched_susp inflated_job_cost sn t := by
              simp only [jobs_that_are_late_or_scheduled_in_sched_susp, List.mem_filter]
              refine ⟨IN0_hp, ?_⟩
              simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true]
              exact ⟨⟨hARR_hp, hCOMP_hp_n⟩, Or.inr hSCHED_hp⟩
            -- j2 = seq_min of filter, j_hp ∈ filter → priority t j2 j_hp
            have h_prio_j2_hp := seq_min_computes_min (higher_eq_priority t)
              (fun x y z => H_priority_is_transitive t y x z)
              _ hTOT_prefix j2 j_hp hBS h_mem_hp
            -- priority t j_hp j1 (HIGHER) + priority t j2 j_hp → priority t j2 j1
            exact H_priority_is_transitive t j_hp j2 j1 h_prio_j2_hp HIGHER
    · -- job_is_late → in filter → seq_min_computes_min
      have h_mem : j1 ∈ jobs_that_are_late_or_scheduled_in_sched_susp job_arrival job_cost arr_seq
          sched_susp inflated_job_cost sn t := by
        simp only [jobs_that_are_late_or_scheduled_in_sched_susp, List.mem_filter]
        refine ⟨IN1, ?_⟩
        simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true]
        exact ⟨⟨ARR1, NOTCOMPn1⟩, Or.inl hLate⟩
      exact seq_min_computes_min (higher_eq_priority t) (fun x y z => H_priority_is_transitive t y x z)
        _ hTOT_prefix j2 j1 hBS h_mem
  · -- SUFFIX case
    push_neg at hLT
    simp only [build_schedule, not_lt.mpr hLT, ↓reduceIte] at hBS
    -- hBS : seq_min (higher_eq_priority t) (pending_jobs ...) = some j2
    have h_mem : j1 ∈ Prosa.Classic.Analysis.Uni.Susp.Sustainability.Allcosts.Reduction.SustainabilityAllCosts.pending_jobs
        job_arrival arr_seq inflated_job_cost sn t := by
      simp only [Prosa.Classic.Analysis.Uni.Susp.Sustainability.Allcosts.Reduction.SustainabilityAllCosts.pending_jobs, List.mem_filter]
      exact ⟨IN1, by simp only [decide_eq_true_eq]; exact ⟨ARR1, NOTCOMPn1⟩⟩
    have hTOT_suffix : ∀ x y : Job,
        x ∈ Prosa.Classic.Analysis.Uni.Susp.Sustainability.Allcosts.Reduction.SustainabilityAllCosts.pending_jobs
          job_arrival arr_seq inflated_job_cost sn t →
        y ∈ Prosa.Classic.Analysis.Uni.Susp.Sustainability.Allcosts.Reduction.SustainabilityAllCosts.pending_jobs
          job_arrival arr_seq inflated_job_cost sn t →
        higher_eq_priority t x y = true ∨ higher_eq_priority t y x = true := by
      intro x y hx hy
      simp only [Prosa.Classic.Analysis.Uni.Susp.Sustainability.Allcosts.Reduction.SustainabilityAllCosts.pending_jobs, List.mem_filter] at hx hy
      exact H_priority_is_total x y t
        (in_arrivals_implies_arrived job_arrival arr_seq H_arrival_times_are_consistent x 0 (t + 1) hx.1)
        (in_arrivals_implies_arrived job_arrival arr_seq H_arrival_times_are_consistent y 0 (t + 1) hy.1)
    exact seq_min_computes_min (higher_eq_priority t) (fun x y z => H_priority_is_transitive t y x z)
      _ hTOT_suffix j2 j1 hBS h_mem

end AdditionalScheduleProperties

section FinalRemarks

include H_arrival_times_are_consistent H_priority_is_reflexive H_priority_is_transitive H_priority_is_total H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_work_conserving H_respects_priority H_respects_self_suspensions H_job_costs_do_not_decrease in
theorem sched_new_is_valid :
    valid_suspension_aware_schedule job_arrival arr_seq higher_eq_priority
      (reduced_suspension_duration job_arrival job_cost arr_seq higher_eq_priority
        sched_susp job_suspension_duration inflated_job_cost j R)
      inflated_job_cost
      (sched_new job_arrival job_cost arr_seq higher_eq_priority
        sched_susp inflated_job_cost j R) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact sched_new_jobs_come_from_arrival_sequence job_arrival job_cost arr_seq
      H_arrival_times_are_consistent higher_eq_priority H_priority_is_reflexive
      H_priority_is_transitive H_priority_is_total sched_susp H_jobs_come_from_arrival_sequence
      job_suspension_duration H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
      H_work_conserving H_respects_priority H_respects_self_suspensions j R inflated_job_cost
      H_job_costs_do_not_decrease
  · exact sched_new_jobs_must_arrive_to_execute job_arrival job_cost arr_seq
      H_arrival_times_are_consistent higher_eq_priority H_priority_is_reflexive
      H_priority_is_transitive H_priority_is_total sched_susp H_jobs_come_from_arrival_sequence
      job_suspension_duration H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
      H_work_conserving H_respects_priority H_respects_self_suspensions j R inflated_job_cost
      H_job_costs_do_not_decrease
  · exact sched_new_completed_jobs_dont_execute job_arrival job_cost arr_seq
      H_arrival_times_are_consistent higher_eq_priority H_priority_is_reflexive
      H_priority_is_transitive H_priority_is_total sched_susp H_jobs_come_from_arrival_sequence
      job_suspension_duration H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
      H_work_conserving H_respects_priority H_respects_self_suspensions j R inflated_job_cost
      H_job_costs_do_not_decrease
  · exact sched_new_work_conserving job_arrival job_cost arr_seq
      H_arrival_times_are_consistent higher_eq_priority H_priority_is_reflexive
      H_priority_is_transitive H_priority_is_total sched_susp H_jobs_come_from_arrival_sequence
      job_suspension_duration H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
      H_work_conserving H_respects_priority H_respects_self_suspensions j R inflated_job_cost
      H_job_costs_do_not_decrease
  · exact sched_new_respects_policy job_arrival job_cost arr_seq
      H_arrival_times_are_consistent higher_eq_priority H_priority_is_reflexive
      H_priority_is_transitive H_priority_is_total sched_susp H_jobs_come_from_arrival_sequence
      job_suspension_duration H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
      H_work_conserving H_respects_priority H_respects_self_suspensions j R inflated_job_cost
      H_job_costs_do_not_decrease
  · exact sched_new_respects_self_suspensions job_arrival job_cost arr_seq
      H_arrival_times_are_consistent higher_eq_priority H_priority_is_reflexive
      H_priority_is_transitive H_priority_is_total sched_susp H_jobs_come_from_arrival_sequence
      job_suspension_duration H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
      H_work_conserving H_respects_priority H_respects_self_suspensions j R inflated_job_cost
      H_job_costs_do_not_decrease

include H_arrival_times_are_consistent H_priority_is_reflexive H_priority_is_transitive H_priority_is_total H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_work_conserving H_respects_priority H_respects_self_suspensions H_job_costs_do_not_decrease in
theorem sched_new_response_time_of_job_j :
    is_response_time_bound_of_job job_arrival inflated_job_cost
      (sched_new job_arrival job_cost arr_seq higher_eq_priority
        sched_susp inflated_job_cost j R) j R →
    is_response_time_bound_of_job job_arrival job_cost sched_susp j R := by
  exact sched_new_jobs_complete_later job_arrival job_cost arr_seq
    H_arrival_times_are_consistent higher_eq_priority H_priority_is_reflexive
    H_priority_is_transitive H_priority_is_total sched_susp H_jobs_come_from_arrival_sequence
    job_suspension_duration H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
    H_work_conserving H_respects_priority H_respects_self_suspensions j R inflated_job_cost
    H_job_costs_do_not_decrease (job_arrival j + R) (le_refl _) j

end FinalRemarks

end ReductionProperties

end SustainabilityAllCostsProperties

end

end Prosa.Classic.Analysis.Uni.Susp.Sustainability.Allcosts.Reduction_properties
