-- Translated from: ../rt-proofs/results/edf/optimality.v
import Prosa.Analysis.Facts.Transform.Edf_opt
import Prosa.Model.Processor.Ideal
import Prosa.Model.Readiness.Basic

namespace Prosa.Results.Edf.Optimality

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
open Prosa.Analysis.Facts.Transform.Edf_opt
open Prosa.Analysis.Facts.Behavior.Arrivals
open Prosa.Analysis.Facts.Behavior.Completion

attribute [local instance] pstate_instance

section Optimality

variable {Job : JobType} [JobCost Job] [JobDeadline Job] [JobArrival Job]
variable [DecidableEq Job]

variable (arr_seq : arrival_sequence Job)
variable (H_arr_seq_valid : valid_arrival_sequence arr_seq)

include H_arr_seq_valid in
theorem EDF_optimality :
    (∃ any_sched : schedule (processor_state Job),
        valid_schedule any_sched arr_seq ∧
        all_deadlines_of_arrivals_met arr_seq any_sched) →
    ∃ edf_sched : schedule (processor_state Job),
        valid_schedule edf_sched arr_seq ∧
        all_deadlines_of_arrivals_met arr_seq edf_sched ∧
        EDF_schedule Job (processor_state Job) edf_sched := by
  intro ⟨sched, ⟨COME, READY⟩, DL_ARR_MET⟩
  have ARR := jobs_must_arrive_to_be_ready sched READY
  have COMP := completed_jobs_are_not_ready sched READY
  have DL_MET := all_deadlines_met_in_valid_schedule arr_seq sched COME DL_ARR_MET
  refine ⟨edf_transform sched, ?_, ?_, ?_⟩
  · exact edf_schedule_is_valid arr_seq H_arr_seq_valid sched ⟨COME, READY⟩ DL_MET
  · exact edf_schedule_meets_all_deadlines_wrt_arrivals arr_seq H_arr_seq_valid sched ⟨COME, READY⟩ DL_ARR_MET
  · exact edf_transform_ensures_edf sched ARR COMP DL_MET

end Optimality

section WeakOptimality

variable {Job : JobType} [JobCost Job] [JobDeadline Job] [JobArrival Job]
variable [DecidableEq Job]

variable (any_sched : schedule (processor_state Job))
variable (H_must_arrive : jobs_must_arrive_to_execute (Job := Job) any_sched)
variable (H_completed_dont_execute : completed_jobs_dont_execute (Job := Job) any_sched)
variable (H_all_deadlines_met : all_deadlines_met (Job := Job) any_sched)

include H_must_arrive H_completed_dont_execute H_all_deadlines_met in
theorem weak_EDF_optimality :
    ∃ edf_sched : schedule (processor_state Job),
      jobs_must_arrive_to_execute (Job := Job) edf_sched ∧
      completed_jobs_dont_execute (Job := Job) edf_sched ∧
      all_deadlines_met (Job := Job) edf_sched ∧
      EDF_schedule Job (processor_state Job) edf_sched ∧
      ∀ j : Job,
          (∃ t, scheduled_at any_sched j t = true) ↔
          (∃ t2, scheduled_at edf_sched j t2 = true) := by
  refine ⟨edf_transform any_sched, ?_, ?_, ?_, ?_, ?_⟩
  · exact edf_transform_jobs_must_arrive any_sched H_must_arrive H_completed_dont_execute H_all_deadlines_met
  · exact edf_transform_completed_jobs_dont_execute any_sched H_must_arrive H_completed_dont_execute H_all_deadlines_met
  · exact edf_transform_deadlines_met any_sched H_must_arrive H_completed_dont_execute H_all_deadlines_met
  · exact edf_transform_ensures_edf any_sched H_must_arrive H_completed_dont_execute H_all_deadlines_met
  · intro j; constructor
    · intro ⟨t, SCHED_j⟩
      exact edf_transform_job_scheduled' any_sched H_must_arrive H_completed_dont_execute H_all_deadlines_met j t SCHED_j
    · intro ⟨t, SCHED_j⟩
      exact edf_transform_job_scheduled any_sched H_must_arrive H_completed_dont_execute H_all_deadlines_met j t SCHED_j

end WeakOptimality

end Prosa.Results.Edf.Optimality
