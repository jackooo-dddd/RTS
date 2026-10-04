-- Authoritative source:
-- ProsaBuddy classic Prosa (prosabuddy commit f692cb7479780cf6009493f373a309e13165201c)
-- source: classic/analysis/uni/susp/sustainability/allcosts/main_claim.v
-- sha256: see Prosa-Shunqi/classic-prosa/comprehensive-classic/file_order.csv (rank 166)

import Prosa.Classic.Util.All
import Prosa.Classic.Model.Priority
import Prosa.Classic.Model.Suspension
import Prosa.Classic.Model.Arrival.Basic.ArrivalSequence
import Prosa.Classic.Model.Schedule.Uni.ResponseTime
import Prosa.Classic.Model.Schedule.Uni.Sustainability
import Prosa.Classic.Model.Schedule.Uni.Susp.SuspensionIntervals
import Prosa.Classic.Model.Schedule.Uni.Susp.Schedule
import Prosa.Classic.Model.Schedule.Uni.Susp.ValidSchedule
import Prosa.Classic.Model.Schedule.Uni.Susp.BuildSuspensionTable
import Prosa.Classic.Model.Schedule.Uni.Susp.Platform
import Prosa.Classic.Analysis.Uni.Susp.Sustainability.Allcosts.Reduction
import Prosa.Classic.Analysis.Uni.Susp.Sustainability.Allcosts.ReductionProperties
import Prosa.Classic.Model.Schedule.Uni.Transformation.Construction

/-!
Weak sustainability with job costs and variable suspension times under the dynamic suspension model (Rocq module
`SustainabilityAllCostsProperty` of `classic/analysis/uni/susp/sustainability/allcosts/main_claim.v`).

Representation notes:
* The section-local `Let`s are unfolded in the statement: `satisfies_suspension_properties`,
  `satisfies_schedule_properties` (whose inner `let`s are inlined), `satisfies_arrival_sequence_properties`,
  `belongs_to_task_model`, `response_time_bounded_by_R` (a Boolean, as `is_response_time_bound_of_job` is),
  `all_params := [JOB_ARRIVAL, JOB_COST, JOB_SUSPENSION]`, `sustainable_param := JOB_COST`,
  `variable_params := [JOB_SUSPENSION]`, `has_better_sustainable_param cost cost' := ∀ j, cost' j ≤ cost j` and
  `weakly_sustainable_with_job_costs_and_variable_suspension_times`.
* The Rocq module aliases `reduction` and `reduction_prop` are the accepted namespaces
  `…Allcosts.Reduction.SustainabilityAllCosts` and `…Allcosts.ReductionProperties.SustainabilityAllCostsProperties`.
* Binder lists follow the Rocq contract (the unused `H_priority_reflexive` is not abstracted). The proof follows the
  Rocq script: the job parameters are replaced by the "bad" parameters (inflated costs, reduced suspension times)
  of the reduced schedule `sched_new`, which belongs to the task model and has the same response time for `j`.
-/

set_option linter.dupNamespace false
set_option linter.unusedVariables false

namespace Prosa.Classic.Analysis.Uni.Susp.Sustainability.Allcosts.MainClaim.SustainabilityAllCostsProperty

open Prosa.Classic.Model.Time.Time
open Prosa.Classic.Model.Arrival.Basic.ArrivalSequence.ArrivalSequence
open Prosa.Classic.Model.Priority.Priority
open Prosa.Classic.Model.Suspension.Suspension
open Prosa.Classic.Model.Schedule.Uni.Schedule.UniprocessorSchedule
open Prosa.Classic.Model.Schedule.Uni.ResponseTime.ResponseTime
open Prosa.Classic.Model.Schedule.Uni.Sustainability.Sustainability
open Prosa.Classic.Model.Schedule.Uni.Susp.SuspensionIntervals.SuspensionIntervals
open Prosa.Classic.Model.Schedule.Uni.Susp.Platform.PlatformWithSuspensions
open Prosa.Classic.Analysis.Uni.Susp.Sustainability.Allcosts.ReductionProperties.SustainabilityAllCostsProperties
open parameter_label

universe u v

theorem policy_is_weakly_sustainable {Task : Type u} [DecidableEq Task] {Job : Type v} [DecidableEq Job]
    (higher_eq_priority : JLDP_policy Job) (H_priority_transitive : JLDP_is_transitive higher_eq_priority)
    (job_task : Job → Task) (task_suspension_bound : Task → duration) (R : time) :
    weakly_sustainable [JOB_ARRIVAL, JOB_COST, JOB_SUSPENSION]
      (fun params sched j =>
        is_response_time_bound_of_job (return_param JOB_ARRIVAL params) (return_param JOB_COST params) sched j R)
      (fun params arr_seq sched =>
        (arrival_times_are_consistent (return_param JOB_ARRIVAL params) arr_seq ∧
          JLDP_is_total arr_seq higher_eq_priority) ∧
        (jobs_come_from_arrival_sequence sched arr_seq ∧
          jobs_must_arrive_to_execute (return_param JOB_ARRIVAL params) sched ∧
          completed_jobs_dont_execute (return_param JOB_COST params) sched ∧
          work_conserving (return_param JOB_ARRIVAL params) (return_param JOB_COST params)
            (return_param JOB_SUSPENSION params) arr_seq sched ∧
          respects_JLDP_policy (return_param JOB_ARRIVAL params) (return_param JOB_COST params)
            (return_param JOB_SUSPENSION params) arr_seq sched higher_eq_priority ∧
          respects_self_suspensions (return_param JOB_ARRIVAL params) (return_param JOB_COST params)
            (return_param JOB_SUSPENSION params) sched) ∧
        dynamic_suspension_model (return_param JOB_COST params) job_task (return_param JOB_SUSPENSION params)
          task_suspension_bound)
      JOB_COST (fun (cost cost' : Job → time) => ∀ j, cost' j ≤ cost j) [JOB_SUSPENSION] := by
  intro params good_params CONS CONS' ONLY BETTER VSCHED good_arr_seq good_sched good_j BELONGS
  obtain ⟨⟨ARRcons, TOTAL⟩, ⟨FROM, MUST, COMPL, WORK, RESP, SELF⟩, DYN⟩ := BELONGS
  obtain ⟨UNIQ, IFF, _⟩ := CONS
  obtain ⟨UNIQ', IFF', _⟩ := CONS'
  -- The job arrival times of both parameter lists coincide.
  have EQarr : return_param JOB_ARRIVAL good_params = return_param JOB_ARRIVAL params := by
    have ARR : JOB_ARRIVAL ∈ labels_of params := (IFF JOB_ARRIVAL).mpr (by simp)
    have ARR' : JOB_ARRIVAL ∈ labels_of good_params := (IFF' JOB_ARRIVAL).mpr (by simp)
    obtain ⟨p, IN, EQ⟩ := List.mem_map.mp ARR
    obtain ⟨p', IN', EQ'⟩ := List.mem_map.mp ARR'
    have EQp := found_param_label params p JOB_ARRIVAL UNIQ IN EQ
    have EQp' := found_param_label good_params p' JOB_ARRIVAL UNIQ' IN' EQ'
    have SAME := ONLY p p' IN IN' (by rw [EQ, EQ']) (by rw [EQ]; simp)
    rw [SAME, EQp'] at EQp
    simp only [job_parameter.param.injEq, true_and] at EQp
    exact eq_of_heq EQp
  have BETTER' : ∀ any_j, return_param JOB_COST good_params any_j ≤ return_param JOB_COST params any_j := BETTER
  -- The reduced schedule and the "bad" job parameters.
  apply sched_new_response_time_of_job_j (return_param JOB_ARRIVAL good_params) (return_param JOB_COST good_params)
    good_arr_seq higher_eq_priority good_sched good_j R (return_param JOB_COST params) BETTER'
  have VS := VSCHED
    [job_parameter.param JOB_ARRIVAL (return_param JOB_ARRIVAL good_params),
      job_parameter.param JOB_COST (return_param JOB_COST params),
      job_parameter.param JOB_SUSPENSION
        (reduction.reduced_suspension_duration (return_param JOB_ARRIVAL good_params)
          (return_param JOB_COST good_params) good_arr_seq higher_eq_priority good_sched
          (return_param JOB_SUSPENSION good_params) (return_param JOB_COST params) good_j R)]
  refine VS ⟨rfl, fun l => Iff.rfl, ?_⟩ ?_ good_arr_seq _ good_j ⟨⟨ARRcons, TOTAL⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro l hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl <;> simp [labels_of]
  · intro P1 P2 IN1 IN2 EQ NOTIN
    simp only [List.mem_cons, List.not_mem_nil, or_false] at IN2
    rcases IN2 with rfl | rfl | rfl
    · rw [found_param_label params P1 JOB_ARRIVAL UNIQ IN1 EQ, EQarr]
    · exact found_param_label params P1 JOB_COST UNIQ IN1 EQ
    · exact absurd (by rw [EQ]; simp) NOTIN
  · exact sched_new_jobs_come_from_arrival_sequence _ _ _ _ _ _ _ _
  · exact sched_new_jobs_must_arrive_to_execute _ _ _ _ _ _ _ _
  · exact sched_new_completed_jobs_dont_execute _ _ _ _ _ _ _ _
  · exact sched_new_work_conserving _ _ _ ARRcons _ _ FROM _ MUST COMPL WORK SELF _ _ _ BETTER'
  · exact sched_new_respects_policy _ _ _ ARRcons _ H_priority_transitive TOTAL _ FROM _ MUST COMPL WORK RESP SELF _ _ _
      BETTER'
  · exact sched_new_respects_self_suspensions _ _ _ _ _ _ MUST COMPL SELF _ _ _ BETTER'
  · intro j0
    exact Nat.le_trans (sched_new_has_shorter_total_suspension _ _ _ _ _ _ MUST COMPL SELF good_j R _ BETTER' j0)
      (DYN j0)

end Prosa.Classic.Analysis.Uni.Susp.Sustainability.Allcosts.MainClaim.SustainabilityAllCostsProperty
