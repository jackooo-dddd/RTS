-- Translated from: ../rt-proofs/classic/implementation/uni/jitter/fp_rta_example.v
import Prosa.Classic.Util.All
import Prosa.Classic.Model.Priority
import Prosa.Classic.Model.Arrival.Basic.Task
import Prosa.Classic.Model.Schedule.Uni.Schedulability
import Prosa.Classic.Model.Arrival.Jitter.Job
import Prosa.Classic.Model.Schedule.Uni.Jitter.Schedule
import Prosa.Classic.Analysis.Uni.Jitter.Workload_bound_fp
import Prosa.Classic.Analysis.Uni.Jitter.Fp_rta_comp
import Prosa.Classic.Implementation.Uni.Jitter.Job
import Prosa.Classic.Implementation.Uni.Jitter.Task
import Prosa.Classic.Implementation.Uni.Jitter.Arrival_sequence
import Prosa.Classic.Implementation.Uni.Jitter.Schedule

namespace Prosa.Classic.Implementation.Uni.Jitter.Fp_rta_example

open Prosa.Classic.Model.Time
open Prosa.Classic.Model.Priority
open Prosa.Classic.Model.Arrival.Basic.Task.SporadicTaskset
open Prosa.Classic.Model.Schedule.Uni.Schedulability
open Prosa.Classic.Model.Arrival.Jitter.Job
open Prosa.Classic.Model.Schedule.Uni.Jitter.Schedule
open Prosa.Classic.Analysis.Uni.Jitter.Workload_bound_fp.WorkloadBoundFP
open Prosa.Classic.Analysis.Uni.Jitter.Fp_rta_comp.ResponseTimeIterationFP
open Prosa.Classic.Implementation.Uni.Jitter.Task.ConcreteTask
open Prosa.Classic.Implementation.Uni.Jitter.Arrival_sequence
open Prosa.Classic.Implementation.Uni.Jitter.Arrival_sequence.ConcreteArrivalSequence
open Prosa.Classic.Implementation.Uni.Jitter.Arrival_sequence.ConcreteJob
open Prosa.Classic.Implementation.Uni.Jitter.Schedule.ConcreteScheduler
open Prosa.Classic.Model.Arrival.Basic.Arrival_sequence

namespace ResponseTimeAnalysisFP

section ExampleRTA

  private def tsk1 : concrete_task := ⟨1, 1, 5, 6, 1⟩
  private def tsk2 : concrete_task := ⟨2, 1, 5, 6, 0⟩
  private def tsk3 : concrete_task := ⟨3, 1, 6, 6, 1⟩

  private def ts : List concrete_task := [tsk1, tsk2, tsk3]

  theorem ts_has_positive_costs :
      ∀ tsk, tsk ∈ ts → tsk.task_cost > 0 := by
    intro tsk h
    simp only [ts, List.mem_cons, List.mem_nil_iff, or_false] at h
    rcases h with rfl | rfl | rfl <;> decide

  theorem ts_has_positive_periods :
      ∀ tsk, tsk ∈ ts → tsk.task_period > 0 := by
    intro tsk h
    simp only [ts, List.mem_cons, List.mem_nil_iff, or_false] at h
    rcases h with rfl | rfl | rfl <;> decide

  private def RTA_claimed_bounds :=
    fp_claimed_bounds
      (fun t => t.task_cost) (fun t => t.task_period) (fun t => t.task_deadline)
      (fun t => t.task_jitter) (RM (fun t => t.task_period)) ts

  private def schedulability_test :=
    fp_schedulable
      (fun t => t.task_cost) (fun t => t.task_period) (fun t => t.task_deadline)
      (fun t => t.task_jitter) (RM (fun t => t.task_period)) ts

  theorem RTA_yields_these_bounds :
      RTA_claimed_bounds = some [(tsk1, 2), (tsk2, 2), (tsk3, 3)] := by native_decide

  theorem schedulability_test_succeeds :
      schedulability_test = true := by native_decide

  private def arr_seq := periodic_arrival_sequence ts

  private def higher_eq_priority :=
    FP_to_JLDP (fun j : concrete_job => j.job_task) (RM (fun t => t.task_period))

  variable (job_jitter : concrete_job → Time)
  variable (H_jitter_is_bounded :
    ∀ j,
      arrives_in arr_seq j →
      job_jitter_leq_task_jitter
        (fun t => t.task_jitter) job_jitter (fun j => j.job_task) j)

  private noncomputable def sched :=
    scheduler (fun j : concrete_job => j.job_arrival) (fun j => j.job_cost)
      job_jitter arr_seq higher_eq_priority

  private def no_deadline_missed_by :=
    task_misses_no_deadline
      (fun j : concrete_job => j.job_arrival) (fun j => j.job_cost)
      (fun j => j.job_deadline) (fun j => j.job_task) arr_seq (sched job_jitter)

  include H_jitter_is_bounded in
  theorem ts_is_schedulable :
      ∀ tsk,
        tsk ∈ ts →
        no_deadline_missed_by job_jitter tsk := by
    intro tsk h_mem
    unfold no_deadline_missed_by
    let tp := fun (t : concrete_task) => t.task_period
    apply taskset_schedulable_by_fp_rta
      (task_cost := fun t => t.task_cost)
      (task_period := tp)
      (task_deadline := fun t => t.task_deadline)
      (task_jitter := fun t => t.task_jitter)
      (job_arrival := fun j => j.job_arrival)
      (job_cost := fun j => j.job_cost)
      (job_deadline := fun j => j.job_deadline)
      (job_jitter := job_jitter)
      (job_task := fun j => j.job_task)
      (ts := ts)
      (arr_seq := arr_seq)
      (sched := sched job_jitter)
      (higher_eq_priority := RM tp)
    · exact ts_has_positive_costs
    · exact ts_has_positive_periods
    · exact periodic_arrivals_are_consistent ts
    · exact periodic_arrivals_is_a_set ts (by native_decide)
    · exact periodic_arrivals_all_jobs_from_taskset ts
    · exact periodic_arrivals_are_sporadic ts
    · exact periodic_arrivals_job_cost_le_task_cost ts
    · exact H_jitter_is_bounded
    · exact periodic_arrivals_job_deadline_eq_task_deadline ts
    · exact RM_is_reflexive tp
    · exact RM_is_transitive tp
    · exact scheduler_jobs_come_from_arrival_sequence
        (fun j : concrete_job => j.job_arrival) (fun j => j.job_cost) job_jitter arr_seq
        (periodic_arrivals_are_consistent ts)
        (periodic_arrivals_is_a_set ts (by native_decide))
        higher_eq_priority
        (fun _t x => by
          simp only [higher_eq_priority, FP_to_JLDP, FP_to_JLFP]
          exact RM_is_reflexive tp x.job_task)
        (fun _t _y x z hxy hyz => by
          simp only [higher_eq_priority, FP_to_JLDP, FP_to_JLFP] at *
          exact RM_is_transitive tp _y.job_task x.job_task z.job_task hxy hyz)
        (fun j1 j2 _t _arr1 _arr2 => by
          simp only [higher_eq_priority, FP_to_JLDP, FP_to_JLFP, RM, decide_eq_true_eq]
          exact le_total _ _)
    · exact scheduler_jobs_execute_after_jitter
        (fun j : concrete_job => j.job_arrival) (fun j => j.job_cost) job_jitter arr_seq
        (periodic_arrivals_are_consistent ts)
        (periodic_arrivals_is_a_set ts (by native_decide))
        higher_eq_priority
        (fun _t x => by
          simp only [higher_eq_priority, FP_to_JLDP, FP_to_JLFP]
          exact RM_is_reflexive tp x.job_task)
        (fun _t _y x z hxy hyz => by
          simp only [higher_eq_priority, FP_to_JLDP, FP_to_JLFP] at *
          exact RM_is_transitive tp _y.job_task x.job_task z.job_task hxy hyz)
        (fun j1 j2 _t _arr1 _arr2 => by
          simp only [higher_eq_priority, FP_to_JLDP, FP_to_JLFP, RM, decide_eq_true_eq]
          exact le_total _ _)
    · exact scheduler_completed_jobs_dont_execute
        (fun j : concrete_job => j.job_arrival) (fun j => j.job_cost) job_jitter arr_seq
        (periodic_arrivals_are_consistent ts)
        (periodic_arrivals_is_a_set ts (by native_decide))
        higher_eq_priority
        (fun _t x => by
          simp only [higher_eq_priority, FP_to_JLDP, FP_to_JLFP]
          exact RM_is_reflexive tp x.job_task)
        (fun _t _y x z hxy hyz => by
          simp only [higher_eq_priority, FP_to_JLDP, FP_to_JLFP] at *
          exact RM_is_transitive tp _y.job_task x.job_task z.job_task hxy hyz)
        (fun j1 j2 _t _arr1 _arr2 => by
          simp only [higher_eq_priority, FP_to_JLDP, FP_to_JLFP, RM, decide_eq_true_eq]
          exact le_total _ _)
    · exact scheduler_work_conserving
        (fun j : concrete_job => j.job_arrival) (fun j => j.job_cost) job_jitter arr_seq
        (periodic_arrivals_are_consistent ts)
        (periodic_arrivals_is_a_set ts (by native_decide))
        higher_eq_priority
        (fun _t x => by
          simp only [higher_eq_priority, FP_to_JLDP, FP_to_JLFP]
          exact RM_is_reflexive tp x.job_task)
        (fun _t _y x z hxy hyz => by
          simp only [higher_eq_priority, FP_to_JLDP, FP_to_JLFP] at *
          exact RM_is_transitive tp _y.job_task x.job_task z.job_task hxy hyz)
        (fun j1 j2 _t _arr1 _arr2 => by
          simp only [higher_eq_priority, FP_to_JLDP, FP_to_JLFP, RM, decide_eq_true_eq]
          exact le_total _ _)
    · exact scheduler_respects_policy
        (fun j : concrete_job => j.job_arrival) (fun j => j.job_cost) job_jitter arr_seq
        (periodic_arrivals_are_consistent ts)
        (periodic_arrivals_is_a_set ts (by native_decide))
        higher_eq_priority
        (fun _t x => by
          simp only [higher_eq_priority, FP_to_JLDP, FP_to_JLFP]
          exact RM_is_reflexive tp x.job_task)
        (fun _t _y x z hxy hyz => by
          simp only [higher_eq_priority, FP_to_JLDP, FP_to_JLFP] at *
          exact RM_is_transitive tp _y.job_task x.job_task z.job_task hxy hyz)
        (fun j1 j2 _t _arr1 _arr2 => by
          simp only [higher_eq_priority, FP_to_JLDP, FP_to_JLFP, RM, decide_eq_true_eq]
          exact le_total _ _)
    · exact schedulability_test_succeeds
    · exact h_mem

end ExampleRTA

end ResponseTimeAnalysisFP

end Prosa.Classic.Implementation.Uni.Jitter.Fp_rta_example
