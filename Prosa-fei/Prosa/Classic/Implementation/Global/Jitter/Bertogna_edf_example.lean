-- Translated from: ../rt-proofs/classic/implementation/global/jitter/bertogna_edf_example.v
import Prosa.Classic.Util.All
import Prosa.Classic.Model.Arrival.Basic.Task
import Prosa.Classic.Model.Priority
import Prosa.Classic.Model.Schedule.Global.Schedulability
import Prosa.Classic.Model.Schedule.Global.Jitter.Job
import Prosa.Classic.Analysis.Global.Jitter.Workload_bound
import Prosa.Classic.Analysis.Global.Jitter.Bertogna_edf_theory
import Prosa.Classic.Analysis.Global.Jitter.Bertogna_edf_comp
import Prosa.Classic.Implementation.Global.Jitter.Job
import Prosa.Classic.Implementation.Global.Jitter.Task
import Prosa.Classic.Implementation.Global.Jitter.Schedule
import Prosa.Classic.Implementation.Global.Jitter.Arrival_sequence
import Mathlib.Tactic

set_option autoImplicit false

namespace Prosa.Classic.Implementation.Global.Jitter.Bertogna_edf_example

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
open Prosa.Classic.Analysis.Global.Jitter.Bertogna_edf_theory.ResponseTimeAnalysisEDFJitter
open Prosa.Classic.Implementation.Global.Jitter.Task.ConcreteTask
open Prosa.Classic.Implementation.Global.Jitter.Task.ConcreteTask.Defs
open Prosa.Classic.Implementation.Global.Jitter.Arrival_sequence.ConcreteArrivalSequence
open Prosa.Classic.Implementation.Global.Jitter.Schedule.ConcreteScheduler
open Prosa.Util.Div_mod

namespace ResponseTimeAnalysisEDF

section ExampleRTA

private def tsk1 : concrete_task :=
  { task_id := 1, task_cost := 2, task_period := 5, task_deadline := 3, task_jitter := 1 }

private def tsk2 : concrete_task :=
  { task_id := 2, task_cost := 4, task_period := 6, task_deadline := 5, task_jitter := 0 }

private def tsk3 : concrete_task :=
  { task_id := 3, task_cost := 2, task_period := 12, task_deadline := 11, task_jitter := 2 }

private def ts : List concrete_task := [tsk1, tsk2, tsk3]

section FactsAboutTaskset

theorem ts_has_valid_parameters :
    valid_sporadic_taskset
      (fun t => t.task_cost) (fun t => t.task_period) (fun t => t.task_deadline) ts := by
  intro tsk IN
  simp only [ts, tsk1, tsk2, tsk3, List.mem_cons, List.mem_nil_iff, or_false] at IN
  rcases IN with rfl | rfl | rfl <;>
    simp [is_valid_sporadic_task, task_cost_positive, task_period_positive,
          task_deadline_positive, task_cost_le_deadline, task_cost_le_period]

theorem ts_has_constrained_deadlines :
    ∀ tsk,
      tsk ∈ ts →
      tsk.task_deadline ≤ tsk.task_period := by
  intro tsk IN
  simp only [ts, tsk1, tsk2, tsk3, List.mem_cons, List.mem_nil_iff, or_false] at IN
  rcases IN with rfl | rfl | rfl <;> simp [tsk1, tsk2, tsk3]

end FactsAboutTaskset

private def num_cpus : ℕ := 2

private noncomputable def edf_response_time_bound
    (rt_bounds : List (concrete_task × Time)) (tsk : concrete_task) (delta : Time) : Time :=
  tsk.task_cost + div_floor
    (total_interference_bound_edf
      (fun t => t.task_cost) (fun t => t.task_period) (fun t => t.task_deadline)
      (fun t => t.task_jitter) tsk rt_bounds delta) num_cpus

private def jitter_plus_R_le_deadline (pair : concrete_task × Time) : Bool :=
  decide (pair.1.task_jitter + pair.2 ≤ pair.1.task_deadline)

private noncomputable def update_bound
    (rt_bounds : List (concrete_task × Time)) (pair : concrete_task × Time) :
    concrete_task × Time :=
  (pair.1, edf_response_time_bound rt_bounds pair.1 pair.2)

private def initial_state (ts' : List concrete_task) : List (concrete_task × Time) :=
  ts'.map (fun t => (t, t.task_cost))

private noncomputable def edf_rta_iteration
    (rt_bounds : List (concrete_task × Time)) : List (concrete_task × Time) :=
  rt_bounds.map (update_bound rt_bounds)

private def max_steps (ts' : List concrete_task) : ℕ :=
  (ts'.map (fun tsk => tsk.task_deadline - tsk.task_cost)).sum + 1

private noncomputable def edf_claimed_bounds (ts' : List concrete_task) :
    Option (List (concrete_task × Time)) :=
  let R_values := (Nat.iterate edf_rta_iteration (max_steps ts') (initial_state ts'))
  if R_values.all jitter_plus_R_le_deadline then some R_values
  else none

private noncomputable def edf_schedulable (ts' : List concrete_task) : Bool :=
  (edf_claimed_bounds ts').isSome

private noncomputable def schedulability_test : List concrete_task → Bool :=
  edf_schedulable

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem schedulability_test_succeeds :
    schedulability_test ts = true := by
  unfold schedulability_test edf_schedulable edf_claimed_bounds ts tsk1 tsk2 tsk3
  simp only [max_steps, List.map, List.sum, initial_state]
  simp only [Nat.iterate, edf_rta_iteration, List.map, update_bound,
    edf_response_time_bound, total_interference_bound_edf,
    interference_bound_edf, interference_bound_generic,
    W_jitter, max_jobs_jitter, edf_specific_interference_bound,
    div_floor, num_cpus, different_task,
    List.filter, List.sum]
  decide

private noncomputable def arr_seq : arrival_sequence concrete_job :=
  periodic_arrival_sequence ts

private noncomputable def sched :=
  scheduler
    (fun j : concrete_job => j.job_arrival)
    (fun j : concrete_job => j.job_cost)
    (fun j : concrete_job => j.job_jitter)
    num_cpus
    arr_seq
    (JLFP_to_JLDP (EDF (fun j : concrete_job => j.job_arrival)
      (fun j : concrete_job => j.job_deadline)))

private noncomputable def no_deadline_missed_by (tsk : concrete_task) : Prop :=
  task_misses_no_deadline
    (fun j : concrete_job => j.job_arrival)
    (fun j : concrete_job => j.job_cost)
    (fun j : concrete_job => j.job_deadline)
    (fun j : concrete_job => j.job_task)
    arr_seq sched tsk

set_option maxRecDepth 8192 in
set_option maxHeartbeats 400000 in
theorem ts_is_schedulable :
    ∀ tsk,
      tsk ∈ ts →
      no_deadline_missed_by tsk := by
  intro tsk h_mem
  unfold no_deadline_missed_by sched arr_seq
  apply Prosa.Classic.Analysis.Global.Jitter.Bertogna_edf_comp.ResponseTimeIterationEDF.taskset_schedulable_by_edf_rta
    (task_cost := fun t : concrete_task => t.task_cost)
    (task_period := fun t : concrete_task => t.task_period)
    (task_deadline := fun t : concrete_task => t.task_deadline)
    (task_jitter := fun t : concrete_task => t.task_jitter)
    (job_arrival := fun j : concrete_job => j.job_arrival)
    (job_cost := fun j : concrete_job => j.job_cost)
    (job_deadline := fun j : concrete_job => j.job_deadline)
    (job_task := fun j : concrete_job => j.job_task)
    (job_jitter := fun j : concrete_job => j.job_jitter)
    (ts := ts)
    (arr_seq := periodic_arrival_sequence ts)
    (sched := scheduler (fun j : concrete_job => j.job_arrival) (fun j : concrete_job => j.job_cost)
      (fun j : concrete_job => j.job_jitter) num_cpus (periodic_arrival_sequence ts)
      (JLFP_to_JLDP (EDF (fun j : concrete_job => j.job_arrival)
        (fun j : concrete_job => j.job_deadline))))
  · exact ts_has_valid_parameters
  · exact ts_has_constrained_deadlines
  · exact periodic_arrivals_all_jobs_from_taskset ts
  · exact periodic_arrivals_valid_job_parameters ts ts_has_valid_parameters
  · exact periodic_arrivals_are_sporadic ts
  · exact (by decide : num_cpus > 0)
  · exact scheduler_jobs_come_from_arrival_sequence
      (fun j : concrete_job => j.job_arrival)
      (fun j : concrete_job => j.job_cost)
      (fun j : concrete_job => j.job_jitter)
      num_cpus (by decide : num_cpus > 0)
      (periodic_arrival_sequence ts)
      (periodic_arrivals_are_consistent ts)
      (periodic_arrivals_is_a_set ts (by native_decide))
      (JLFP_to_JLDP (EDF (fun j : concrete_job => j.job_arrival) (fun j : concrete_job => j.job_deadline)))
      (by intro t y x z hxy hyz; exact EDF_is_transitive _ _ y x z hxy hyz)
      (by intro t x y; unfold JLFP_to_JLDP; simp only [EDF, decide_eq_true_eq]; exact le_total _ _)
  · exact scheduler_jobs_execute_after_jitter
      (fun j : concrete_job => j.job_arrival)
      (fun j : concrete_job => j.job_cost)
      (fun j : concrete_job => j.job_jitter)
      num_cpus (by decide : num_cpus > 0)
      (periodic_arrival_sequence ts)
      (periodic_arrivals_are_consistent ts)
      (periodic_arrivals_is_a_set ts (by native_decide))
      (JLFP_to_JLDP (EDF (fun j : concrete_job => j.job_arrival) (fun j : concrete_job => j.job_deadline)))
      (by intro t y x z hxy hyz; exact EDF_is_transitive _ _ y x z hxy hyz)
      (by intro t x y; unfold JLFP_to_JLDP; simp only [EDF, decide_eq_true_eq]; exact le_total _ _)
  · exact scheduler_completed_jobs_dont_execute
      (fun j : concrete_job => j.job_arrival)
      (fun j : concrete_job => j.job_cost)
      (fun j : concrete_job => j.job_jitter)
      num_cpus (by decide : num_cpus > 0)
      (periodic_arrival_sequence ts)
      (periodic_arrivals_are_consistent ts)
      (periodic_arrivals_is_a_set ts (by native_decide))
      (JLFP_to_JLDP (EDF (fun j : concrete_job => j.job_arrival) (fun j : concrete_job => j.job_deadline)))
      (by intro t y x z hxy hyz; exact EDF_is_transitive _ _ y x z hxy hyz)
      (by intro t x y; unfold JLFP_to_JLDP; simp only [EDF, decide_eq_true_eq]; exact le_total _ _)
  · exact scheduler_sequential_jobs
      (fun j : concrete_job => j.job_arrival)
      (fun j : concrete_job => j.job_cost)
      (fun j : concrete_job => j.job_jitter)
      num_cpus (by decide : num_cpus > 0)
      (periodic_arrival_sequence ts)
      (periodic_arrivals_are_consistent ts)
      (periodic_arrivals_is_a_set ts (by native_decide))
      (JLFP_to_JLDP (EDF (fun j : concrete_job => j.job_arrival) (fun j : concrete_job => j.job_deadline)))
      (by intro t y x z hxy hyz; exact EDF_is_transitive _ _ y x z hxy hyz)
      (by intro t x y; unfold JLFP_to_JLDP; simp only [EDF, decide_eq_true_eq]; exact le_total _ _)
  · exact scheduler_work_conserving
      (fun j : concrete_job => j.job_arrival)
      (fun j : concrete_job => j.job_cost)
      (fun j : concrete_job => j.job_jitter)
      num_cpus (by decide : num_cpus > 0)
      (periodic_arrival_sequence ts)
      (periodic_arrivals_are_consistent ts)
      (periodic_arrivals_is_a_set ts (by native_decide))
      (JLFP_to_JLDP (EDF (fun j : concrete_job => j.job_arrival) (fun j : concrete_job => j.job_deadline)))
      (by intro t y x z hxy hyz; exact EDF_is_transitive _ _ y x z hxy hyz)
      (by intro t x y; unfold JLFP_to_JLDP; simp only [EDF, decide_eq_true_eq]; exact le_total _ _)
  · -- respects_JLFP_policy_edf
    intro j j_hp t h_arr h_back h_sched
    exact scheduler_respects_policy
      (fun j : concrete_job => j.job_arrival)
      (fun j : concrete_job => j.job_cost)
      (fun j : concrete_job => j.job_jitter)
      num_cpus (by decide : num_cpus > 0)
      (periodic_arrival_sequence ts)
      (periodic_arrivals_are_consistent ts)
      (periodic_arrivals_is_a_set ts (by native_decide))
      (JLFP_to_JLDP (EDF (fun j : concrete_job => j.job_arrival) (fun j : concrete_job => j.job_deadline)))
      (by intro t' y x z hxy hyz; exact EDF_is_transitive _ _ y x z hxy hyz)
      (by intro t' x y; unfold JLFP_to_JLDP; simp only [EDF, decide_eq_true_eq]; exact le_total _ _)
      j j_hp t h_arr h_back h_sched
  · -- H_test_succeeds: edf_schedulable (comp's Prop version)
    unfold Prosa.Classic.Analysis.Global.Jitter.Bertogna_edf_comp.ResponseTimeIterationEDF.edf_schedulable
    unfold Prosa.Classic.Analysis.Global.Jitter.Bertogna_edf_comp.ResponseTimeIterationEDF.edf_claimed_bounds
    unfold Prosa.Classic.Analysis.Global.Jitter.Bertogna_edf_comp.ResponseTimeIterationEDF.edf_rta_iteration
    unfold Prosa.Classic.Analysis.Global.Jitter.Bertogna_edf_comp.ResponseTimeIterationEDF.update_bound
    unfold Prosa.Classic.Analysis.Global.Jitter.Bertogna_edf_comp.ResponseTimeIterationEDF.edf_response_time_bound
    unfold Prosa.Classic.Analysis.Global.Jitter.Bertogna_edf_comp.ResponseTimeIterationEDF.jitter_plus_R_le_deadline
    simp only [ts, tsk1, tsk2, tsk3, num_cpus,
      total_interference_bound_edf, interference_bound_edf,
      interference_bound_generic, edf_specific_interference_bound,
      W_jitter, max_jobs_jitter, div_floor, different_task,
      List.sum, Ne]
    decide
  · exact h_mem

end ExampleRTA

end ResponseTimeAnalysisEDF

end Prosa.Classic.Implementation.Global.Jitter.Bertogna_edf_example
