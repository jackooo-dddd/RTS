-- Translated from: ../rt-proofs/classic/analysis/uni/susp/sustainability/allcosts/main_claim.v
import Prosa.Classic.Util.All
import Prosa.Classic.Model.Priority
import Prosa.Classic.Model.Suspension
import Prosa.Classic.Model.Arrival.Basic.Arrival_sequence
import Prosa.Classic.Model.Schedule.Uni.Response_time
import Prosa.Classic.Model.Schedule.Uni.Sustainability
import Prosa.Classic.Model.Schedule.Uni.Susp.Suspension_intervals
import Prosa.Classic.Model.Schedule.Uni.Susp.Schedule
import Prosa.Classic.Model.Schedule.Uni.Susp.Platform
import Prosa.Classic.Analysis.Uni.Susp.Sustainability.Allcosts.Reduction
import Prosa.Classic.Analysis.Uni.Susp.Sustainability.Allcosts.Reduction_properties
import Prosa.Classic.Model.Schedule.Uni.Transformation.Construction
import Mathlib.Tactic

namespace Prosa.Classic.Analysis.Uni.Susp.Sustainability.Allcosts.Main_claim

open Prosa.Classic.Model.Time
open Prosa.Classic.Model.Schedule.Uni.Schedule
open Prosa.Classic.Model.Schedule.Uni.Susp.Suspension_intervals
open Prosa.Classic.Model.Schedule.Uni.Susp.Platform.PlatformWithSuspensions
open Prosa.Classic.Model.Schedule.Uni.Response_time.ResponseTime
open Prosa.Classic.Model.Schedule.Uni.Sustainability
open Prosa.Classic.Model.Suspension
open Prosa.Classic.Model.Priority
open Prosa.Classic.Model.Arrival.Basic.Arrival_sequence
open Prosa.Classic.Analysis.Uni.Susp.Sustainability.Allcosts.Reduction.SustainabilityAllCosts
open Prosa.Classic.Analysis.Uni.Susp.Sustainability.Allcosts.Reduction_properties.SustainabilityAllCostsProperties
open Classical

attribute [local instance] propDecidable

noncomputable section

namespace SustainabilityAllCostsProperty

section SustainabilityProperty

variable {Task : Type _} [DecidableEq Task]
variable {Job : Type _} [DecidableEq Job]

variable (higher_eq_priority : JLDP_policy Job)
variable (H_priority_reflexive : JLDP_is_reflexive higher_eq_priority)
variable (H_priority_transitive : JLDP_is_transitive higher_eq_priority)

variable (job_task : Job → Task)
variable (task_suspension_bound : Task → Duration)

private def satisfies_suspension_properties
    (params : List (job_parameter Job)) : Prop :=
  dynamic_suspension_model
    (return_param Job parameter_label.JOB_COST params)
    job_task
    (return_param Job parameter_label.JOB_SUSPENSION params)
    task_suspension_bound

private def satisfies_schedule_properties
    (params : List (job_parameter Job))
    (arr_seq : arrival_sequence Job)
    (sched : schedule Job) : Prop :=
  let job_arrival := return_param Job parameter_label.JOB_ARRIVAL params
  let job_cost := return_param Job parameter_label.JOB_COST params
  let job_suspension_duration := return_param Job parameter_label.JOB_SUSPENSION params
  jobs_come_from_arrival_sequence sched arr_seq ∧
  jobs_must_arrive_to_execute job_arrival sched ∧
  completed_jobs_dont_execute job_cost sched ∧
  work_conserving job_arrival job_cost job_suspension_duration arr_seq sched ∧
  respects_JLDP_policy job_arrival job_cost job_suspension_duration arr_seq
    sched higher_eq_priority ∧
  respects_self_suspensions job_arrival job_cost job_suspension_duration sched

private def satisfies_arrival_sequence_properties
    (params : List (job_parameter Job))
    (arr_seq : arrival_sequence Job) : Prop :=
  arrival_times_are_consistent
    (return_param Job parameter_label.JOB_ARRIVAL params) arr_seq ∧
  JLDP_is_total arr_seq higher_eq_priority

private def belongs_to_task_model'
    (params : List (job_parameter Job))
    (arr_seq : arrival_sequence Job)
    (sched : schedule Job) : Prop :=
  satisfies_arrival_sequence_properties higher_eq_priority params arr_seq ∧
  satisfies_schedule_properties higher_eq_priority params arr_seq sched ∧
  satisfies_suspension_properties job_task task_suspension_bound params

variable (R : Time)

private def response_time_bounded_by_R
    (params : List (job_parameter Job))
    (sched : schedule Job)
    (j : Job) : Bool :=
  decide (is_response_time_bound_of_job
    (return_param Job parameter_label.JOB_ARRIVAL params)
    (return_param Job parameter_label.JOB_COST params)
    sched j R)

private def all_params' : List parameter_label :=
  [parameter_label.JOB_ARRIVAL, parameter_label.JOB_COST, parameter_label.JOB_SUSPENSION]

private def sustainable_param' : parameter_label := parameter_label.JOB_COST

private def variable_params' : List parameter_label := [parameter_label.JOB_SUSPENSION]

private def has_better_sustainable_param
    (cost cost' : Job → Time) : Prop :=
  ∀ j, cost j ≥ cost' j

private abbrev weakly_sustainable_with_job_costs_and_variable_suspension_times : Prop :=
  weakly_sustainable Job all_params'
    (response_time_bounded_by_R R)
    (belongs_to_task_model' higher_eq_priority job_task task_suspension_bound)
    sustainable_param' has_better_sustainable_param variable_params'

include H_priority_reflexive H_priority_transitive

include H_priority_reflexive H_priority_transitive in
theorem policy_is_weakly_sustainable :
    weakly_sustainable_with_job_costs_and_variable_suspension_times
      higher_eq_priority job_task task_suspension_bound R := by
  -- Unfold the top-level definition
  unfold weakly_sustainable_with_job_costs_and_variable_suspension_times
  unfold weakly_sustainable
  intro params good_params CONS CONS' ONLY BETTER VSCHED
  unfold jobs_are_schedulable_with
  intro good_arr_seq good_sched good_j BELONGS
  unfold belongs_to_task_model' at BELONGS
  obtain ⟨⟨H_arr_consistent, H_total⟩, ⟨H_from_arr, H_must_arr, H_compl, H_wc, H_resp_pri, H_resp_susp⟩, H_susp_model⟩ := BELONGS
  set job_arrival := return_param Job parameter_label.JOB_ARRIVAL good_params with job_arrival_def
  set good_cost := return_param Job parameter_label.JOB_COST good_params with good_cost_def
  set bad_cost := return_param Job parameter_label.JOB_COST params with bad_cost_def
  set good_suspension := return_param Job parameter_label.JOB_SUSPENSION good_params with good_suspension_def
  -- Show that JOB_ARRIVAL parameters are equal
  have EQarr : job_arrival = return_param Job parameter_label.JOB_ARRIVAL params := by
    unfold differ_only_by at ONLY
    obtain ⟨UNIQ, IFF, _⟩ := CONS
    obtain ⟨UNIQ', IFF', _⟩ := CONS'
    have ARR : parameter_label.JOB_ARRIVAL ∈ labels_of Job params := by
      rw [IFF]; simp [all_params']
    have ARR' : parameter_label.JOB_ARRIVAL ∈ labels_of Job good_params := by
      rw [IFF']; simp [all_params']
    simp [labels_of] at ARR ARR'
    obtain ⟨p, hp_mem, hp_label⟩ := ARR
    obtain ⟨p', hp'_mem, hp'_label⟩ := ARR'
    have EQp := found_param_label Job params p parameter_label.JOB_ARRIVAL UNIQ hp_mem hp_label
    have EQp' := found_param_label Job good_params p' parameter_label.JOB_ARRIVAL UNIQ' hp'_mem hp'_label
    -- ONLY : p ∈ params → p' ∈ good_params → p.label = p'.label → p.label ∉ [JOB_COST] → p = p'
    have NOTIN : p.p_label ∉ [parameter_label.JOB_COST] := by
      rw [hp_label]; simp [sustainable_param']
    have EQ_pp := ONLY p p' hp_mem hp'_mem (by rw [hp_label, hp'_label]) NOTIN
    -- EQ_pp : p = p'
    -- Substituting: param ... (return_param ... params) = param ... (return_param ... good_params)
    have h1 : param Job parameter_label.JOB_ARRIVAL (return_param Job parameter_label.JOB_ARRIVAL params) =
              param Job parameter_label.JOB_ARRIVAL (return_param Job parameter_label.JOB_ARRIVAL good_params) := by
      rw [← EQp, ← EQp', EQ_pp]
    -- Extract the function from the param equality
    have h2 := congr_arg (fun p => get_param_function Job parameter_label.JOB_ARRIVAL p) h1
    simp [param, get_param_function] at h2
    exact h2.symm
  -- Set up the constructed schedule and suspension
  set bad_sched := sched_new job_arrival good_cost good_arr_seq higher_eq_priority
    good_sched bad_cost good_j R with bad_sched_def
  set reduced_susp := reduced_suspension_duration job_arrival good_cost
    good_arr_seq higher_eq_priority good_sched good_suspension bad_cost good_j R with reduced_susp_def
  set bad_params : List (job_parameter Job) :=
    [param Job parameter_label.JOB_ARRIVAL job_arrival,
     param Job parameter_label.JOB_COST bad_cost,
     param Job parameter_label.JOB_SUSPENSION reduced_susp]
  -- Helper lemma for return_param on bad_params
  have h_rp_arr : return_param Job parameter_label.JOB_ARRIVAL bad_params = job_arrival := by
    simp only [bad_params]
    unfold return_param find_param get_param_function param List.findIdx List.getD
    simp only [List.findIdx.go, BEq.beq, default_val]
    rfl
  have h_rp_cost : return_param Job parameter_label.JOB_COST bad_params = bad_cost := by
    simp only [bad_params]
    unfold return_param find_param get_param_function param List.findIdx List.getD
    simp only [List.findIdx.go, BEq.beq, default_val]
    rfl
  have h_rp_susp : return_param Job parameter_label.JOB_SUSPENSION bad_params = reduced_susp := by
    simp only [bad_params]
    unfold return_param find_param get_param_function param List.findIdx List.getD
    simp only [List.findIdx.go, BEq.beq, default_val]
    rfl
  -- Apply sched_new_response_time_of_job_j to reduce the goal
  unfold response_time_bounded_by_R
  simp only [decide_eq_true_eq]
  apply sched_new_response_time_of_job_j job_arrival good_cost good_arr_seq
    H_arr_consistent higher_eq_priority H_priority_reflexive H_priority_transitive H_total
    good_sched H_from_arr good_suspension H_must_arr H_compl H_wc H_resp_pri H_resp_susp
    good_j R bad_cost (by intro any_j; exact BETTER any_j)
  -- Now need: is_response_time_bound_of_job job_arrival bad_cost bad_sched good_j R
  -- Use VSCHED with bad_params
  unfold jobs_are_V_schedulable_with at VSCHED
  -- Show bad_params has consistent labels
  have bad_params_consistent : has_consistent_labels Job all_params' sustainable_param' variable_params' bad_params := by
    simp only [bad_params]
    refine ⟨?_, ?_, ?_⟩
    · -- has_unique_labels
      unfold has_unique_labels labels_of
      simp only [List.map_cons, param, List.map_nil]
      exact List.nodup_cons.mpr ⟨by simp [List.mem_cons, List.mem_singleton], List.nodup_cons.mpr ⟨by simp [List.mem_singleton], List.nodup_cons.mpr ⟨by simp, List.nodup_nil⟩⟩⟩
    · -- corresponding_labels
      unfold corresponding_labels labels_of
      intro l
      simp only [List.map_cons, param, List.map_nil, List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false]
      simp only [all_params', List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false]
    · -- sustainable_and_varying_params_in
      unfold sustainable_and_varying_params_in sustainable_param' variable_params'
      intro label hl
      unfold labels_of
      simp only [List.map_cons, param, List.map_nil, List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false]
      simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hl
      rcases hl with rfl | rfl <;> simp
  -- Show differ_only_by Job variable_params' params bad_params
  have bad_params_diff : differ_only_by Job variable_params' params bad_params := by
    simp only [bad_params]
    unfold differ_only_by variable_params'
    intro p1 p2 hIN1 hIN2 hEQ hNOTIN
    simp only [param, List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hIN2
    obtain ⟨UNIQ_P, _, _⟩ := CONS
    rcases hIN2 with rfl | rfl | rfl
    · -- p2 has label JOB_ARRIVAL
      have hEQ' : p1.p_label = parameter_label.JOB_ARRIVAL := hEQ
      rw [EQarr]
      exact found_param_label Job params p1 parameter_label.JOB_ARRIVAL UNIQ_P hIN1 hEQ'
    · -- p2 has label JOB_COST
      have hEQ' : p1.p_label = parameter_label.JOB_COST := hEQ
      exact found_param_label Job params p1 parameter_label.JOB_COST UNIQ_P hIN1 hEQ'
    · -- p2 has label JOB_SUSPENSION — contradiction with hNOTIN
      exfalso
      apply hNOTIN
      simp only [List.mem_singleton]
      exact hEQ
  -- Get schedulability for bad_params
  have SCHED_BAD := VSCHED bad_params bad_params_consistent bad_params_diff
  unfold jobs_are_schedulable_with at SCHED_BAD
  -- Apply with bad_sched
  suffices h_belongs : belongs_to_task_model' higher_eq_priority job_task task_suspension_bound bad_params good_arr_seq bad_sched by
    have RES := SCHED_BAD good_arr_seq bad_sched good_j h_belongs
    unfold response_time_bounded_by_R at RES
    simp only [decide_eq_true_eq] at RES
    rw [h_rp_arr, h_rp_cost] at RES
    exact RES
  -- Prove belongs_to_task_model'
  have H_cost_inflate : ∀ any_j, bad_cost any_j ≥ good_cost any_j := by
    intro any_j; exact BETTER any_j
  simp only [belongs_to_task_model', satisfies_arrival_sequence_properties,
    satisfies_schedule_properties, satisfies_suspension_properties]
  rw [h_rp_arr, h_rp_cost, h_rp_susp]
  exact ⟨⟨H_arr_consistent, H_total⟩,
    ⟨sched_new_jobs_come_from_arrival_sequence job_arrival good_cost good_arr_seq
      H_arr_consistent higher_eq_priority H_priority_reflexive H_priority_transitive H_total
      good_sched H_from_arr good_suspension H_must_arr H_compl H_wc H_resp_pri H_resp_susp
      good_j R bad_cost H_cost_inflate,
     sched_new_jobs_must_arrive_to_execute job_arrival good_cost good_arr_seq
      H_arr_consistent higher_eq_priority H_priority_reflexive H_priority_transitive H_total
      good_sched H_from_arr good_suspension H_must_arr H_compl H_wc H_resp_pri H_resp_susp
      good_j R bad_cost H_cost_inflate,
     sched_new_completed_jobs_dont_execute job_arrival good_cost good_arr_seq
      H_arr_consistent higher_eq_priority H_priority_reflexive H_priority_transitive H_total
      good_sched H_from_arr good_suspension H_must_arr H_compl H_wc H_resp_pri H_resp_susp
      good_j R bad_cost H_cost_inflate,
     sched_new_work_conserving job_arrival good_cost good_arr_seq
      H_arr_consistent higher_eq_priority H_priority_reflexive H_priority_transitive H_total
      good_sched H_from_arr good_suspension H_must_arr H_compl H_wc H_resp_pri H_resp_susp
      good_j R bad_cost H_cost_inflate,
     sched_new_respects_policy job_arrival good_cost good_arr_seq
      H_arr_consistent higher_eq_priority H_priority_reflexive H_priority_transitive H_total
      good_sched H_from_arr good_suspension H_must_arr H_compl H_wc H_resp_pri H_resp_susp
      good_j R bad_cost H_cost_inflate,
     sched_new_respects_self_suspensions job_arrival good_cost good_arr_seq
      H_arr_consistent higher_eq_priority H_priority_reflexive H_priority_transitive H_total
      good_sched H_from_arr good_suspension H_must_arr H_compl H_wc H_resp_pri H_resp_susp
      good_j R bad_cost H_cost_inflate⟩,
    fun j0 => Nat.le_trans
      (sched_new_has_shorter_total_suspension job_arrival good_cost good_arr_seq
        H_arr_consistent higher_eq_priority H_priority_reflexive H_priority_transitive H_total
        good_sched H_from_arr good_suspension H_must_arr H_compl H_wc H_resp_pri H_resp_susp
        good_j R bad_cost H_cost_inflate j0)
      (H_susp_model j0)⟩

end SustainabilityProperty

end SustainabilityAllCostsProperty

end

end Prosa.Classic.Analysis.Uni.Susp.Sustainability.Allcosts.Main_claim
