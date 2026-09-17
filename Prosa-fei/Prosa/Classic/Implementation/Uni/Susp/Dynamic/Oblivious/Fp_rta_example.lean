-- Translated from: ../rt-proofs/classic/implementation/uni/susp/dynamic/oblivious/fp_rta_example.v
import Prosa.Classic.Util.All
import Prosa.Classic.Model.Arrival.Basic.Job
import Prosa.Classic.Model.Arrival.Basic.Task
import Prosa.Classic.Model.Priority
import Prosa.Classic.Model.Schedule.Uni.Schedule
import Prosa.Classic.Model.Schedule.Uni.Schedulability
import Prosa.Classic.Model.Schedule.Uni.Susp.Suspension_intervals
import Prosa.Classic.Model.Suspension
import Prosa.Classic.Analysis.Uni.Basic.Workload_bound_fp
import Prosa.Classic.Analysis.Uni.Basic.Fp_rta_comp
import Prosa.Classic.Analysis.Uni.Susp.Dynamic.Oblivious.Fp_rta
import Prosa.Classic.Analysis.Uni.Susp.Dynamic.Oblivious.Reduction
import Prosa.Classic.Implementation.Uni.Susp.Dynamic.Job
import Prosa.Classic.Implementation.Uni.Susp.Dynamic.Task
import Prosa.Classic.Implementation.Uni.Susp.Dynamic.Arrival_sequence
import Prosa.Classic.Implementation.Uni.Susp.Schedule
import Mathlib.Tactic

namespace Prosa.Classic.Implementation.Uni.Susp.Dynamic.Oblivious.Fp_rta_example

open Prosa.Classic.Model.Time
open Prosa.Classic.Model.Arrival.Basic.Job
open Prosa.Classic.Model.Arrival.Basic.Task.SporadicTaskset
open Prosa.Classic.Model.Arrival.Basic.Arrival_sequence
open Prosa.Classic.Model.Priority
open Prosa.Classic.Model.Schedule.Uni.Schedule
open Prosa.Classic.Model.Schedule.Uni.Schedulability
  hiding schedule scheduled_at service_at service_during service completed_by
    completed_jobs_dont_execute completion_monotonic
open Prosa.Classic.Model.Schedule.Uni.Susp.Suspension_intervals
open Prosa.Classic.Model.Suspension
open Prosa.Classic.Analysis.Uni.Basic.Workload_bound_fp.WorkloadBoundFP
open Prosa.Classic.Analysis.Uni.Basic.Fp_rta_comp.ResponseTimeIterationFP
open Prosa.Classic.Analysis.Uni.Susp.Dynamic.Oblivious.Fp_rta.SuspensionObliviousFP
open Prosa.Classic.Analysis.Uni.Susp.Dynamic.Oblivious.Reduction.ReductionToBasicSchedule
open Prosa.Classic.Implementation.Uni.Susp.Dynamic.Task.ConcreteTask
open Prosa.Classic.Implementation.Uni.Susp.Dynamic.Arrival_sequence.ConcreteArrivalSequence
open Prosa.Classic.Implementation.Uni.Susp.Schedule.ConcreteScheduler

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace ResponseTimeAnalysisFP

section ExampleRTA

private def tsk1 : concrete_task :=
  { task_id := 1, task_cost := 1, task_period := 5,
    task_deadline := 5, task_suspension_bound := 1 }

private def tsk2 : concrete_task :=
  { task_id := 2, task_cost := 1, task_period := 5,
    task_deadline := 5, task_suspension_bound := 0 }

private def tsk3 : concrete_task :=
  { task_id := 3, task_cost := 1, task_period := 6,
    task_deadline := 6, task_suspension_bound := 1 }

private def ts : List concrete_task := [tsk1, tsk2, tsk3]

theorem ts_has_valid_parameters :
    valid_sporadic_taskset
      concrete_task.task_cost concrete_task.task_period concrete_task.task_deadline ts := by
  intro tsk IN
  simp only [ts, List.mem_cons, List.mem_nil_iff, or_false] at IN
  rcases IN with rfl | rfl | rfl <;>
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp_all [tsk1, tsk2, tsk3,
      Model.Arrival.Basic.Task.SporadicTask.task_cost_positive,
      Model.Arrival.Basic.Task.SporadicTask.task_period_positive,
      Model.Arrival.Basic.Task.SporadicTask.task_deadline_positive,
      Model.Arrival.Basic.Task.SporadicTask.task_cost_le_deadline,
      Model.Arrival.Basic.Task.SporadicTask.task_cost_le_period,
      concrete_task.task_cost, concrete_task.task_period, concrete_task.task_deadline]

private def inflated_cost :=
  inflated_task_cost concrete_task.task_cost concrete_task.task_suspension_bound

theorem inflated_cost_le_deadline_and_period :
    forall tsk,
      tsk ∈ ts →
      inflated_cost tsk ≤ concrete_task.task_deadline tsk ∧
      inflated_cost tsk ≤ concrete_task.task_period tsk := by
  intro tsk IN
  simp [ts, tsk1, tsk2, tsk3] at IN
  rcases IN with rfl | rfl | rfl <;>
    simp [inflated_cost, inflated_task_cost, concrete_task.task_cost,
          concrete_task.task_suspension_bound, concrete_task.task_deadline,
          concrete_task.task_period, tsk1, tsk2, tsk3]

private def RTA_claimed_bounds :=
  fp_claimed_bounds inflated_cost concrete_task.task_period concrete_task.task_deadline
    (RM concrete_task.task_period)

private def schedulability_test :=
  fp_schedulable inflated_cost concrete_task.task_period concrete_task.task_deadline
    (RM concrete_task.task_period)

theorem RTA_yields_these_bounds :
    RTA_claimed_bounds ts = some [(tsk1, 3), (tsk2, 3), (tsk3, 5)] := by
  native_decide

theorem schedulability_test_succeeds :
    schedulability_test ts := by
  simp [schedulability_test, fp_schedulable]
  rw [show fp_claimed_bounds inflated_cost concrete_task.task_period concrete_task.task_deadline
    (RM concrete_task.task_period) ts = RTA_claimed_bounds ts from rfl]
  rw [RTA_yields_these_bounds]
  simp

private abbrev arr_seq := periodic_arrival_sequence ts

variable (next_suspension : job_suspension concrete_job)
variable (H_dynamic_suspensions :
  dynamic_suspension_model concrete_job.job_cost concrete_job.job_task
    next_suspension concrete_task.task_suspension_bound)

private abbrev higher_eq_priority :=
  FP_to_JLDP concrete_job.job_task (RM concrete_task.task_period)

private abbrev sched' (ns : job_suspension concrete_job) :=
  scheduler concrete_job.job_arrival concrete_job.job_cost arr_seq ns higher_eq_priority

private abbrev no_deadline_missed_by (ns : job_suspension concrete_job) :=
  task_misses_no_deadline concrete_job.job_arrival concrete_job.job_cost
    concrete_job.job_deadline concrete_job.job_task arr_seq (sched' ns)

include H_dynamic_suspensions in
theorem ts_is_schedulable :
    forall tsk,
      tsk ∈ ts →
      no_deadline_missed_by next_suspension tsk := by
  intro tsk IN
  unfold no_deadline_missed_by sched' arr_seq higher_eq_priority
  set jldp := FP_to_JLDP concrete_job.job_task (RM concrete_task.task_period)
  have h_consistent := periodic_arrivals_are_consistent ts ts_has_valid_parameters
  have h_jldp_trans : JLDP_is_transitive jldp :=
    fun t y x z hxy hyz =>
      RM_is_transitive concrete_task.task_period
        (concrete_job.job_task y) (concrete_job.job_task x) (concrete_job.job_task z) hxy hyz
  have h_jldp_total : JLDP_is_total (periodic_arrival_sequence ts) jldp := by
    intro j1 j2 t _ _
    change RM concrete_task.task_period (concrete_job.job_task j1) (concrete_job.job_task j2) = true ∨
           RM concrete_task.task_period (concrete_job.job_task j2) (concrete_job.job_task j1) = true
    simp only [RM, decide_eq_true_eq]
    exact Nat.le_total _ _
  apply suspension_oblivious_fp_rta_implies_schedulability
    (task_cost := concrete_task.task_cost)
    (task_period := concrete_task.task_period)
    (task_deadline := concrete_task.task_deadline)
    (job_cost := concrete_job.job_cost)
    (job_deadline := concrete_job.job_deadline)
    (job_task := concrete_job.job_task)
    (higher_eq_priority := RM concrete_task.task_period)
    (task_suspension_bound := concrete_task.task_suspension_bound)
  · exact ts_has_valid_parameters
  · exact h_consistent
  · exact periodic_arrivals_is_a_set ts ts_has_valid_parameters (by decide)
  · intro j hj; exact periodic_arrivals_all_jobs_from_taskset ts ts_has_valid_parameters j hj
  · exact periodic_arrivals_valid_job_parameters ts ts_has_valid_parameters
  · exact periodic_arrivals_are_sporadic ts ts_has_valid_parameters
  · exact RM_is_reflexive concrete_task.task_period
  · exact RM_is_transitive concrete_task.task_period
  · intro t1 t2 _ _; simp only [RM, decide_eq_true_eq]; exact Nat.le_total _ _
  · exact H_dynamic_suspensions
  · exact inflated_cost_le_deadline_and_period
  · exact scheduler_jobs_come_from_arrival_sequence
      concrete_job.job_arrival concrete_job.job_cost
      (periodic_arrival_sequence ts) h_consistent next_suspension jldp
  · exact scheduler_jobs_must_arrive_to_execute
      concrete_job.job_arrival concrete_job.job_cost
      (periodic_arrival_sequence ts) next_suspension jldp
  · exact scheduler_completed_jobs_dont_execute
      concrete_job.job_arrival concrete_job.job_cost
      (periodic_arrival_sequence ts) next_suspension jldp
  · exact scheduler_work_conserving
      concrete_job.job_arrival concrete_job.job_cost
      (periodic_arrival_sequence ts) h_consistent next_suspension jldp
  · exact scheduler_respects_policy
      concrete_job.job_arrival concrete_job.job_cost
      (periodic_arrival_sequence ts) h_consistent next_suspension jldp
      h_jldp_trans h_jldp_total
  · exact scheduler_respects_self_suspensions
      concrete_job.job_arrival concrete_job.job_cost
      (periodic_arrival_sequence ts) next_suspension jldp
  · exact schedulability_test_succeeds
  · exact IN


end ExampleRTA

end ResponseTimeAnalysisFP

end

end Prosa.Classic.Implementation.Uni.Susp.Dynamic.Oblivious.Fp_rta_example
