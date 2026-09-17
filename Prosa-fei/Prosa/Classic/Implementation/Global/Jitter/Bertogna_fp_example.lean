-- Translated from: ../rt-proofs/classic/implementation/global/jitter/bertogna_fp_example.v
import Prosa.Classic.Util.All
import Prosa.Classic.Model.Arrival.Basic.Task
import Prosa.Classic.Model.Priority
import Prosa.Classic.Model.Schedule.Global.Schedulability
import Prosa.Classic.Model.Schedule.Global.Jitter.Job
import Prosa.Classic.Analysis.Global.Jitter.Workload_bound
import Prosa.Classic.Analysis.Global.Jitter.Interference_bound_fp
import Prosa.Classic.Analysis.Global.Jitter.Bertogna_fp_theory
import Prosa.Classic.Analysis.Global.Jitter.Bertogna_fp_comp
import Prosa.Classic.Implementation.Global.Jitter.Job
import Prosa.Classic.Implementation.Global.Jitter.Task
import Prosa.Classic.Implementation.Global.Jitter.Schedule
import Prosa.Classic.Implementation.Global.Jitter.Arrival_sequence
import Mathlib.Tactic

set_option autoImplicit false

namespace Prosa.Classic.Implementation.Global.Jitter.Bertogna_fp_example

open Prosa.Classic.Model.Time
open Prosa.Classic.Model.Arrival.Basic.Job
open Prosa.Classic.Model.Arrival.Basic.Task.SporadicTask
open Prosa.Classic.Model.Arrival.Basic.Task.SporadicTaskset
open Prosa.Classic.Model.Arrival.Basic.Arrival_sequence
open Prosa.Classic.Model.Priority
open Prosa.Classic.Model.Schedule.Global.Schedulability.Schedulability
open Prosa.Classic.Model.Schedule.Global.Jitter.Job
open Prosa.Classic.Model.Schedule.Global.Basic.Schedule.Schedule
open Prosa.Classic.Analysis.Global.Jitter.Workload_bound.WorkloadBoundJitter
open Prosa.Classic.Analysis.Global.Jitter.Bertogna_fp_theory.ResponseTimeAnalysisFP
open Prosa.Classic.Implementation.Global.Jitter.Task.ConcreteTask
open Prosa.Classic.Implementation.Global.Jitter.Task.ConcreteTask.Defs
open Prosa.Classic.Implementation.Global.Jitter.Arrival_sequence.ConcreteArrivalSequence
open Prosa.Classic.Implementation.Global.Jitter.Schedule.ConcreteScheduler
open Prosa.Util.Div_mod

namespace ResponseTimeAnalysisFP

section ResponseTimeIterationFP

variable {sporadic_task : Type} [DecidableEq sporadic_task]
variable (task_cost : sporadic_task → Time)
variable (task_period : sporadic_task → Time)
variable (task_deadline : sporadic_task → Time)
variable (task_jitter : sporadic_task → Time)
variable (num_cpus : ℕ)
noncomputable def per_task_rta (tsk : sporadic_task)
    (R_prev : List (sporadic_task × Time)) (step : ℕ) : Time :=
  (fun t => task_cost tsk +
    div_floor
      (total_interference_bound_fp task_cost task_period task_jitter tsk R_prev t)
      num_cpus)^[step] (task_cost tsk)

def max_steps (tsk : sporadic_task) : ℕ :=
  task_deadline tsk - task_cost tsk + 1

noncomputable def fp_bound_of_task
    (hp_pairs : Option (List (sporadic_task × Time)))
    (tsk : sporadic_task) : Option (List (sporadic_task × Time)) :=
  match hp_pairs with
  | some rt_bounds =>
    let R := per_task_rta task_cost task_period task_jitter num_cpus tsk rt_bounds
                (max_steps task_cost task_deadline tsk)
    if task_jitter tsk + R ≤ task_deadline tsk then
      some (rt_bounds ++ [(tsk, R)])
    else none
  | none => none

noncomputable def fp_claimed_bounds (ts : List sporadic_task) :
    Option (List (sporadic_task × Time)) :=
  ts.foldl (fp_bound_of_task task_cost task_period task_deadline task_jitter num_cpus) (some [])

noncomputable def fp_schedulable (ts : List sporadic_task) : Bool :=
  (fp_claimed_bounds task_cost task_period task_deadline task_jitter num_cpus ts).isSome

end ResponseTimeIterationFP

section TasksetSchedulableByFpRta

variable {sporadic_task : Type} [DecidableEq sporadic_task]
variable (task_cost : sporadic_task → Time)
variable (task_period : sporadic_task → Time)
variable (task_deadline : sporadic_task → Time)
variable (task_jitter : sporadic_task → Time)
variable {Job : Type} [DecidableEq Job]
variable (job_arrival : Job → Time)
variable (job_cost : Job → Time)
variable (job_deadline : Job → Time)
variable (job_task : Job → sporadic_task)
variable (job_jitter : Job → Time)
variable (ts : List sporadic_task)
variable (arr_seq : arrival_sequence Job)
variable {num_cpus : ℕ}
variable (sched : schedule Job num_cpus)
variable (higher_priority : FP_policy sporadic_task)

theorem taskset_schedulable_by_fp_rta
    (H_valid_task_parameters :
      valid_sporadic_taskset task_cost task_period task_deadline ts)
    (H_constrained_deadlines :
      ∀ tsk, tsk ∈ ts → task_deadline tsk ≤ task_period tsk)
    (H_task_set_is_sorted :
      List.IsChain (fun a b => higher_priority a b = true) ts)
    (H_unique_priorities :
      FP_is_antisymmetric_over_task_set higher_priority ts)
    (H_total_priority :
      FP_is_total_over_task_set higher_priority ts)
    (H_priority_transitive :
      FP_is_transitive higher_priority)
    (H_all_jobs_from_taskset :
      ∀ j, arrives_in arr_seq j → job_task j ∈ ts)
    (H_valid_job_parameters :
      ∀ j, arrives_in arr_seq j →
        valid_sporadic_job_with_jitter task_cost task_deadline task_jitter job_cost
                                       job_deadline job_task job_jitter j)
    (H_sporadic_tasks :
      Prosa.Classic.Model.Arrival.Basic.Task_arrival.sporadic_task_model
        task_period job_arrival job_task arr_seq)
    (H_at_least_one_cpu : num_cpus > 0)
    (H_jobs_come_from_arrival_sequence :
      jobs_come_from_arrival_sequence sched arr_seq)
    (H_jobs_execute_after_jitter :
      Prosa.Classic.Model.Schedule.Global.Jitter.Schedule.ScheduleWithJitter.jobs_execute_after_jitter
        job_arrival job_jitter sched)
    (H_completed_jobs_dont_execute :
      completed_jobs_dont_execute job_cost sched)
    (H_sequential_jobs : sequential_jobs sched)
    (H_work_conserving :
      Prosa.Classic.Model.Schedule.Global.Jitter.Platform.work_conserving
        job_arrival job_cost job_jitter arr_seq sched)
    (H_respects_policy :
      Prosa.Classic.Model.Schedule.Global.Jitter.Constrained_deadlines.respects_FP_policy_jitter
        job_arrival job_cost job_task job_jitter arr_seq sched higher_priority)
    (H_test_succeeds :
      fp_schedulable task_cost task_period task_deadline task_jitter num_cpus ts = true) :
    ∀ tsk, tsk ∈ ts →      task_misses_no_deadline job_arrival job_cost job_deadline job_task arr_seq sched tsk := by
  -- Establish definitional equality between local and comp fp_claimed_bounds
  have h_eq : fp_claimed_bounds task_cost task_period task_deadline task_jitter num_cpus ts =
      Prosa.Classic.Analysis.Global.Jitter.Bertogna_fp_comp.ResponseTimeIterationFP.fp_claimed_bounds
        task_cost task_period task_deadline task_jitter num_cpus ts := by
    unfold fp_claimed_bounds fp_bound_of_task per_task_rta max_steps
    unfold Prosa.Classic.Analysis.Global.Jitter.Bertogna_fp_comp.ResponseTimeIterationFP.fp_claimed_bounds
           Prosa.Classic.Analysis.Global.Jitter.Bertogna_fp_comp.ResponseTimeIterationFP.fp_bound_of_task
           Prosa.Classic.Analysis.Global.Jitter.Bertogna_fp_comp.ResponseTimeIterationFP.per_task_rta
           Prosa.Classic.Analysis.Global.Jitter.Bertogna_fp_comp.ResponseTimeIterationFP.max_steps
    rfl
  have h_test_prop : Prosa.Classic.Analysis.Global.Jitter.Bertogna_fp_comp.ResponseTimeIterationFP.fp_schedulable
      task_cost task_period task_deadline task_jitter num_cpus ts := by
    unfold Prosa.Classic.Analysis.Global.Jitter.Bertogna_fp_comp.ResponseTimeIterationFP.fp_schedulable
    rw [← h_eq]
    simp only [fp_schedulable] at H_test_succeeds
    exact Option.isSome_iff_ne_none.mp (by rw [H_test_succeeds])
  exact Prosa.Classic.Analysis.Global.Jitter.Bertogna_fp_comp.ResponseTimeIterationFP.taskset_schedulable_by_fp_rta
    task_cost task_period task_deadline task_jitter
    job_arrival job_cost job_deadline job_task job_jitter
    higher_priority ts
    H_valid_task_parameters H_constrained_deadlines
    H_task_set_is_sorted
    H_unique_priorities H_total_priority H_priority_transitive
    arr_seq H_all_jobs_from_taskset
    H_valid_job_parameters
    H_sporadic_tasks
    sched
    H_at_least_one_cpu
    H_jobs_come_from_arrival_sequence
    H_jobs_execute_after_jitter
    H_completed_jobs_dont_execute
    H_sequential_jobs
    H_work_conserving H_respects_policy h_test_prop

end TasksetSchedulableByFpRta

section ExampleRTA

private def tsk1 : concrete_task :=
  { task_id := 1, task_cost := 2, task_period := 5, task_deadline := 3, task_jitter := 0 }

private def tsk2 : concrete_task :=
  { task_id := 2, task_cost := 4, task_period := 6, task_deadline := 5, task_jitter := 1 }

private def tsk3 : concrete_task :=
  { task_id := 3, task_cost := 3, task_period := 12, task_deadline := 11, task_jitter := 2 }

private def ts : List concrete_task := [tsk1, tsk2, tsk3]

section FactsAboutTaskset

theorem ts_has_valid_parameters :
    valid_sporadic_taskset
      (fun t => t.task_cost) (fun t => t.task_period) (fun t => t.task_deadline) ts := by
  intro tsk h_in
  simp [ts, tsk1, tsk2, tsk3] at h_in
  rcases h_in with rfl | rfl | rfl <;>
    simp [is_valid_sporadic_task, task_cost_positive, task_period_positive,
          task_deadline_positive, task_cost_le_deadline, task_cost_le_period]

theorem ts_has_constrained_deadlines :
    ∀ tsk,
      tsk ∈ ts →      tsk.task_deadline ≤ tsk.task_period := by
  intro tsk h_in
  simp [ts, tsk1, tsk2, tsk3] at h_in
  rcases h_in with rfl | rfl | rfl <;> simp [tsk1, tsk2, tsk3]

end FactsAboutTaskset

private def num_cpus : ℕ := 2

private noncomputable def schedulability_test :=
  fp_schedulable
    (fun t : concrete_task => t.task_cost)
    (fun t : concrete_task => t.task_period)
    (fun t : concrete_task => t.task_deadline)
    (fun t : concrete_task => t.task_jitter)
    num_cpus

theorem schedulability_test_succeeds :
    schedulability_test ts = true := by
  unfold schedulability_test fp_schedulable fp_claimed_bounds ts tsk1 tsk2 tsk3
  simp [List.foldl, fp_bound_of_task, per_task_rta, max_steps,
        total_interference_bound_fp, interference_bound_generic,
        W_jitter, max_jobs_jitter, div_floor, num_cpus,
        List.map, List.sum]

private noncomputable def arr_seq : arrival_sequence concrete_job :=
  periodic_arrival_sequence ts

private def higher_priority :=
  FP_to_JLDP (fun j : concrete_job => j.job_task) (RM (fun t : concrete_task => t.task_period))

section FactsAboutPriorityOrder

theorem ts_has_unique_priorities :
    FP_is_antisymmetric_over_task_set (RM (fun t : concrete_task => t.task_period)) ts := by
  intro x1 x2 h1 h2 hp1 hp2
  simp [RM] at hp1 hp2
  simp [ts, tsk1, tsk2, tsk3] at h1 h2
  rcases h1 with rfl | rfl | rfl <;> rcases h2 with rfl | rfl | rfl <;>
    simp_all [tsk1, tsk2, tsk3]

theorem priority_is_total :
    FP_is_total_over_task_set (RM (fun t : concrete_task => t.task_period)) ts := by
  intro x1 x2 h1 h2
  unfold RM
  simp only [decide_eq_true_eq]
  simp [ts, tsk1, tsk2, tsk3] at h1 h2
  rcases h1 with rfl | rfl | rfl <;> rcases h2 with rfl | rfl | rfl <;>
    simp [tsk1, tsk2, tsk3] <;> omega

end FactsAboutPriorityOrder

private noncomputable def sched :=
  scheduler
    (fun j : concrete_job => j.job_arrival)
    (fun j : concrete_job => j.job_cost)
    (fun j : concrete_job => j.job_jitter)
    num_cpus
    arr_seq
    higher_priority

private noncomputable def no_deadline_missed_by (tsk : concrete_task) : Prop :=
  task_misses_no_deadline
    (fun j : concrete_job => j.job_arrival)
    (fun j : concrete_job => j.job_cost)
    (fun j : concrete_job => j.job_deadline)
    (fun j : concrete_job => j.job_task)
    arr_seq sched tsk

theorem ts_is_schedulable :
    ∀ tsk,
      tsk ∈ ts →      no_deadline_missed_by tsk := by
  intro tsk h_in
  unfold no_deadline_missed_by sched higher_priority arr_seq
  apply taskset_schedulable_by_fp_rta
    (fun t : concrete_task => t.task_cost)
    (fun t : concrete_task => t.task_period)
    (fun t : concrete_task => t.task_deadline)
    (fun t : concrete_task => t.task_jitter)
    (fun j : concrete_job => j.job_arrival)
    (fun j : concrete_job => j.job_cost)
    (fun j : concrete_job => j.job_deadline)
    (fun j : concrete_job => j.job_task)
    (fun j : concrete_job => j.job_jitter)
    ts (periodic_arrival_sequence ts)
    (sched := scheduler (fun j : concrete_job => j.job_arrival) (fun j : concrete_job => j.job_cost)
      (fun j : concrete_job => j.job_jitter) num_cpus (periodic_arrival_sequence ts)
      (FP_to_JLDP (fun j : concrete_job => j.job_task) (RM (fun t : concrete_task => t.task_period))))
    (RM (fun t : concrete_task => t.task_period))
  · exact ts_has_valid_parameters
  · exact ts_has_constrained_deadlines
  · -- ts is sorted by RM priority
    simp [ts, tsk1, tsk2, tsk3, RM, List.IsChain]
  · exact ts_has_unique_priorities
  · exact priority_is_total
  · exact RM_is_transitive _
  · exact periodic_arrivals_all_jobs_from_taskset ts
  · exact periodic_arrivals_valid_job_parameters ts ts_has_valid_parameters
  · exact periodic_arrivals_are_sporadic ts
  · exact (by decide : num_cpus > 0)
  · exact Prosa.Classic.Implementation.Global.Jitter.Schedule.ConcreteScheduler.scheduler_jobs_come_from_arrival_sequence
      (fun j : concrete_job => j.job_arrival)
      (fun j : concrete_job => j.job_cost)
      (fun j : concrete_job => j.job_jitter)
      num_cpus (by unfold num_cpus; omega)
      (periodic_arrival_sequence ts)
      (periodic_arrivals_are_consistent ts)
      (periodic_arrivals_is_a_set ts (by native_decide))
      (FP_to_JLDP (fun j : concrete_job => j.job_task)
        (RM (fun t : concrete_task => t.task_period)))
      (fun t y x z hxy hyz => by
        simp only [FP_to_JLDP, FP_to_JLFP] at *
        exact RM_is_transitive _ (y.job_task) (x.job_task) (z.job_task) hxy hyz)
      (fun t x y => by
        simp only [FP_to_JLDP, FP_to_JLFP, RM]
        simp only [decide_eq_true_eq]
        exact Nat.le_total _ _)
  · exact Prosa.Classic.Implementation.Global.Jitter.Schedule.ConcreteScheduler.scheduler_jobs_execute_after_jitter
      (fun j : concrete_job => j.job_arrival)
      (fun j : concrete_job => j.job_cost)
      (fun j : concrete_job => j.job_jitter)
      num_cpus (by unfold num_cpus; omega)
      (periodic_arrival_sequence ts)
      (periodic_arrivals_are_consistent ts)
      (periodic_arrivals_is_a_set ts (by native_decide))
      (FP_to_JLDP (fun j : concrete_job => j.job_task)
        (RM (fun t : concrete_task => t.task_period)))
      (fun t y x z hxy hyz => by
        simp only [FP_to_JLDP, FP_to_JLFP] at *
        exact RM_is_transitive _ (y.job_task) (x.job_task) (z.job_task) hxy hyz)
      (fun t x y => by
        simp only [FP_to_JLDP, FP_to_JLFP, RM]
        simp only [decide_eq_true_eq]
        exact Nat.le_total _ _)
  · exact Prosa.Classic.Implementation.Global.Jitter.Schedule.ConcreteScheduler.scheduler_completed_jobs_dont_execute
      (fun j : concrete_job => j.job_arrival)
      (fun j : concrete_job => j.job_cost)
      (fun j : concrete_job => j.job_jitter)
      num_cpus (by unfold num_cpus; omega)
      (periodic_arrival_sequence ts)
      (periodic_arrivals_are_consistent ts)
      (periodic_arrivals_is_a_set ts (by native_decide))
      (FP_to_JLDP (fun j : concrete_job => j.job_task)
        (RM (fun t : concrete_task => t.task_period)))
      (fun t y x z hxy hyz => by
        simp only [FP_to_JLDP, FP_to_JLFP] at *
        exact RM_is_transitive _ (y.job_task) (x.job_task) (z.job_task) hxy hyz)
      (fun t x y => by
        simp only [FP_to_JLDP, FP_to_JLFP, RM]
        simp only [decide_eq_true_eq]
        exact Nat.le_total _ _)
  · exact Prosa.Classic.Implementation.Global.Jitter.Schedule.ConcreteScheduler.scheduler_sequential_jobs
      (fun j : concrete_job => j.job_arrival)
      (fun j : concrete_job => j.job_cost)
      (fun j : concrete_job => j.job_jitter)
      num_cpus (by unfold num_cpus; omega)
      (periodic_arrival_sequence ts)
      (periodic_arrivals_are_consistent ts)
      (periodic_arrivals_is_a_set ts (by native_decide))
      (FP_to_JLDP (fun j : concrete_job => j.job_task)
        (RM (fun t : concrete_task => t.task_period)))
      (fun t y x z hxy hyz => by
        simp only [FP_to_JLDP, FP_to_JLFP] at *
        exact RM_is_transitive _ (y.job_task) (x.job_task) (z.job_task) hxy hyz)
      (fun t x y => by
        simp only [FP_to_JLDP, FP_to_JLFP, RM]
        simp only [decide_eq_true_eq]
        exact Nat.le_total _ _)
  · exact Prosa.Classic.Implementation.Global.Jitter.Schedule.ConcreteScheduler.scheduler_work_conserving
      (fun j : concrete_job => j.job_arrival)
      (fun j : concrete_job => j.job_cost)
      (fun j : concrete_job => j.job_jitter)
      num_cpus (by unfold num_cpus; omega)
      (periodic_arrival_sequence ts)
      (periodic_arrivals_are_consistent ts)
      (periodic_arrivals_is_a_set ts (by native_decide))
      (FP_to_JLDP (fun j : concrete_job => j.job_task)
        (RM (fun t : concrete_task => t.task_period)))
      (fun t y x z hxy hyz => by
        simp only [FP_to_JLDP, FP_to_JLFP] at *
        exact RM_is_transitive _ (y.job_task) (x.job_task) (z.job_task) hxy hyz)
      (fun t x y => by
        simp only [FP_to_JLDP, FP_to_JLFP, RM]
        simp only [decide_eq_true_eq]
        exact Nat.le_total _ _)
  · exact Prosa.Classic.Implementation.Global.Jitter.Schedule.ConcreteScheduler.scheduler_respects_policy
      (fun j : concrete_job => j.job_arrival)
      (fun j : concrete_job => j.job_cost)
      (fun j : concrete_job => j.job_jitter)
      num_cpus (by unfold num_cpus; omega)
      (periodic_arrival_sequence ts)
      (periodic_arrivals_are_consistent ts)
      (periodic_arrivals_is_a_set ts (by native_decide))
      (FP_to_JLDP (fun j : concrete_job => j.job_task)
        (RM (fun t : concrete_task => t.task_period)))
      (fun t y x z hxy hyz => by
        simp only [FP_to_JLDP, FP_to_JLFP] at *
        exact RM_is_transitive _ (y.job_task) (x.job_task) (z.job_task) hxy hyz)
      (fun t x y => by
        simp only [FP_to_JLDP, FP_to_JLFP, RM]
        simp only [decide_eq_true_eq]
        exact Nat.le_total _ _)
  · exact schedulability_test_succeeds
  · exact h_in

end ExampleRTA

end ResponseTimeAnalysisFP

end Prosa.Classic.Implementation.Global.Jitter.Bertogna_fp_example
