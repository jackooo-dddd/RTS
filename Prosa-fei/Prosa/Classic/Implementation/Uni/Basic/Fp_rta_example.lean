-- Translated from: ../rt-proofs/classic/implementation/uni/basic/fp_rta_example.v
import Prosa.Classic.Util.All
import Prosa.Classic.Model.Arrival.Basic.Job
import Prosa.Classic.Model.Arrival.Basic.Task
import Prosa.Classic.Model.Priority
import Prosa.Classic.Model.Schedule.Uni.Schedule
import Prosa.Classic.Model.Schedule.Uni.Schedulability
import Prosa.Classic.Analysis.Uni.Basic.Workload_bound_fp
import Prosa.Classic.Analysis.Uni.Basic.Fp_rta_comp
import Prosa.Classic.Implementation.Job
import Prosa.Classic.Implementation.Task
import Prosa.Classic.Implementation.Arrival_sequence
import Prosa.Classic.Implementation.Uni.Basic.Schedule

namespace Prosa.Classic.Implementation.Uni.Basic.Fp_rta_example

open Prosa.Classic.Model.Time
open Prosa.Classic.Model.Arrival.Basic.Job
open Prosa.Classic.Model.Arrival.Basic.Arrival_sequence
open Prosa.Classic.Model.Arrival.Basic.Task.SporadicTask
open Prosa.Classic.Model.Arrival.Basic.Task.SporadicTaskset
open Prosa.Classic.Model.Priority
open Prosa.Classic.Model.Schedule.Uni.Schedule
open Prosa.Classic.Model.Schedule.Uni.Schedulability hiding schedule scheduled_at service_at service_during service completed_by completed_jobs_dont_execute completion_monotonic
open Prosa.Classic.Analysis.Uni.Basic.Workload_bound_fp.WorkloadBoundFP
open Prosa.Classic.Analysis.Uni.Basic.Fp_rta_comp.ResponseTimeIterationFP
open Prosa.Classic.Implementation.Job.ConcreteJob
open Prosa.Classic.Implementation.Task.ConcreteTask
open Prosa.Classic.Implementation.Arrival_sequence.ConcreteArrivalSequence
open Prosa.Classic.Implementation.Uni.Basic.Schedule.ConcreteScheduler

namespace ResponseTimeAnalysisFP

section ExampleRTA

private abbrev task_cost : concrete_task → Time := fun t => t.task_cost
private abbrev task_period : concrete_task → Time := fun t => t.task_period
private abbrev task_deadline : concrete_task → Time := fun t => t.task_deadline
private abbrev job_arrival : concrete_job → Time := fun j => j.job_arrival
private abbrev job_cost : concrete_job → Time := fun j => j.job_cost
private abbrev job_deadline' : concrete_job → Time := fun j => j.job_deadline
private abbrev job_task : concrete_job → concrete_task := fun j => j.job_task

private def tsk1 : concrete_task := ⟨1, 1, 4, 5⟩
private def tsk2 : concrete_task := ⟨2, 1, 6, 5⟩
private def tsk3 : concrete_task := ⟨3, 1, 6, 6⟩

private def ts : List concrete_task := [tsk1, tsk2, tsk3]

theorem ts_has_valid_parameters :
    valid_sporadic_taskset task_cost task_period task_deadline ts := by
  intro tsk IN
  simp [ts, tsk1, tsk2, tsk3] at IN
  rcases IN with rfl | rfl | rfl <;>
    simp [is_valid_sporadic_task, task_cost_positive, task_period_positive,
          task_deadline_positive, task_cost_le_deadline, task_cost_le_period,
          task_cost, task_period, task_deadline]

private def RTA_claimed_bounds (ts : List concrete_task) :=
  fp_claimed_bounds task_cost task_period task_deadline (RM task_period) ts

private def schedulability_test (ts : List concrete_task) :=
  fp_schedulable task_cost task_period task_deadline (RM task_period) ts

theorem RTA_yields_these_bounds :
    RTA_claimed_bounds ts = some [(tsk1, 1), (tsk2, 3), (tsk3, 3)] := by
  native_decide

theorem schedulability_test_succeeds :
    schedulability_test ts := by
  simp only [schedulability_test, fp_schedulable]
  rw [show fp_claimed_bounds task_cost task_period task_deadline (RM task_period) ts = some [(tsk1, 1), (tsk2, 3), (tsk3, 3)] from RTA_yields_these_bounds]
  simp

private def arr_seq := periodic_arrival_sequence ts

private def higher_eq_priority : JLDP_policy concrete_job :=
  FP_to_JLDP job_task (RM task_period)

theorem priority_is_total :
    ∀ t, ∀ x y : concrete_job, higher_eq_priority t x y = true ∨ higher_eq_priority t y x = true := by
  intro t x y
  simp only [higher_eq_priority, FP_to_JLDP, FP_to_JLFP, RM, decide_eq_true_eq]
  exact le_total _ _

private def sched := scheduler job_arrival job_cost arr_seq higher_eq_priority

private def no_deadline_missed_by :=
  task_misses_no_deadline job_arrival job_cost job_deadline' job_task arr_seq sched

theorem ts_is_schedulable :
    ∀ tsk,
      tsk ∈ ts →
      no_deadline_missed_by tsk := by
  intro tsk h_mem
  unfold no_deadline_missed_by
  apply taskset_schedulable_by_fp_rta
    (task_cost := task_cost)
    (task_period := task_period)
    (task_deadline := task_deadline)
    (job_arrival := job_arrival)
    (job_cost := job_cost)
    (job_deadline := job_deadline')
    (job_task := job_task)
    (ts := ts)
    (arr_seq := arr_seq)
    (sched := sched)
    (higher_eq_priority := RM task_period)
  · exact ts_has_valid_parameters
  · exact periodic_arrivals_are_consistent ts
  · exact periodic_arrivals_is_a_set ts (by native_decide)
  · exact periodic_arrivals_all_jobs_from_taskset ts
  · exact periodic_arrivals_valid_job_parameters ts ts_has_valid_parameters
  · exact periodic_arrivals_are_sporadic ts
  · exact RM_is_reflexive task_period
  · exact RM_is_transitive task_period
  · exact scheduler_jobs_come_from_arrival_sequence job_arrival job_cost arr_seq
      (periodic_arrivals_are_consistent ts)
      (periodic_arrivals_is_a_set ts (by native_decide))
      higher_eq_priority
      (fun _t _y x z hxy hyz => by
        simp only [higher_eq_priority, FP_to_JLDP, FP_to_JLFP] at *
        exact RM_is_transitive task_period (job_task _y) (job_task x) (job_task z) hxy hyz)
      (fun _t x y => priority_is_total _t x y)
  · exact scheduler_jobs_must_arrive_to_execute job_arrival job_cost arr_seq
      (periodic_arrivals_are_consistent ts)
      (periodic_arrivals_is_a_set ts (by native_decide))
      higher_eq_priority
      (fun _t _y x z hxy hyz => by
        simp only [higher_eq_priority, FP_to_JLDP, FP_to_JLFP] at *
        exact RM_is_transitive task_period (job_task _y) (job_task x) (job_task z) hxy hyz)
      (fun _t x y => priority_is_total _t x y)
  · exact scheduler_completed_jobs_dont_execute job_arrival job_cost arr_seq
      (periodic_arrivals_are_consistent ts)
      (periodic_arrivals_is_a_set ts (by native_decide))
      higher_eq_priority
      (fun _t _y x z hxy hyz => by
        simp only [higher_eq_priority, FP_to_JLDP, FP_to_JLFP] at *
        exact RM_is_transitive task_period (job_task _y) (job_task x) (job_task z) hxy hyz)
      (fun _t x y => priority_is_total _t x y)
  · exact scheduler_work_conserving job_arrival job_cost arr_seq
      (periodic_arrivals_are_consistent ts)
      (periodic_arrivals_is_a_set ts (by native_decide))
      higher_eq_priority
      (fun _t _y x z hxy hyz => by
        simp only [higher_eq_priority, FP_to_JLDP, FP_to_JLFP] at *
        exact RM_is_transitive task_period (job_task _y) (job_task x) (job_task z) hxy hyz)
      (fun _t x y => priority_is_total _t x y)
  · exact scheduler_respects_policy job_arrival job_cost arr_seq
      (periodic_arrivals_are_consistent ts)
      (periodic_arrivals_is_a_set ts (by native_decide))
      higher_eq_priority
      (fun _t _y x z hxy hyz => by
        simp only [higher_eq_priority, FP_to_JLDP, FP_to_JLFP] at *
        exact RM_is_transitive task_period (job_task _y) (job_task x) (job_task z) hxy hyz)
      (fun _t x y => priority_is_total _t x y)
  · exact schedulability_test_succeeds
  · exact h_mem

end ExampleRTA

end ResponseTimeAnalysisFP

end Prosa.Classic.Implementation.Uni.Basic.Fp_rta_example
