-- Translated from: ../rt-proofs/classic/implementation/apa/bertogna_edf_example.v
import Prosa.Classic.Util.All
import Prosa.Classic.Model.Arrival.Basic.Job
import Prosa.Classic.Model.Arrival.Basic.Task
import Prosa.Classic.Model.Priority
import Prosa.Classic.Model.Schedule.Global.Schedulability
import Prosa.Classic.Model.Schedule.Global.Basic.Schedule
import Prosa.Classic.Model.Schedule.Apa.Affinity
import Prosa.Classic.Analysis.Apa.Workload_bound
import Prosa.Classic.Analysis.Apa.Bertogna_edf_comp
import Prosa.Classic.Implementation.Apa.Job
import Prosa.Classic.Implementation.Apa.Task
import Prosa.Classic.Implementation.Apa.Schedule
import Prosa.Classic.Implementation.Apa.Arrival_sequence
import Prosa.Classic.Model.Arrival.Basic.Arrival_sequence
import Prosa.Classic.Model.Arrival.Basic.Task_arrival
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

set_option autoImplicit false

namespace Prosa.Classic.Implementation.Apa.Bertogna_edf_example

open Prosa.Classic.Model.Time
open Prosa.Classic.Model.Arrival.Basic.Job
open Prosa.Classic.Model.Arrival.Basic.Task
open Prosa.Classic.Model.Arrival.Basic.Task.SporadicTask
open Prosa.Classic.Model.Arrival.Basic.Task.SporadicTaskset
open Prosa.Classic.Model.Arrival.Basic.Arrival_sequence
open Prosa.Classic.Model.Arrival.Basic.Task_arrival
open Prosa.Classic.Model.Priority
open Prosa.Classic.Model.Schedule.Global.Schedulability
open Prosa.Classic.Model.Schedule.Global.Schedulability.Schedulability
open Prosa.Classic.Model.Schedule.Global.Basic.Schedule
open Prosa.Classic.Model.Schedule.Global.Basic.Schedule.Schedule
open Prosa.Classic.Model.Schedule.Global.Basic.Schedule.ScheduleOfSporadicTask
open Prosa.Classic.Model.Schedule.Apa.Affinity
open Prosa.Classic.Analysis.Apa.Workload_bound
open Prosa.Classic.Analysis.Apa.Workload_bound.WorkloadBound
open Prosa.Classic.Implementation.Apa.Task.ConcreteTask
open Prosa.Classic.Implementation.Apa.Schedule.ConcreteScheduler
open Prosa.Classic.Implementation.Apa.Arrival_sequence.ConcreteArrivalSequence
open Prosa.Classic.Analysis.Apa.Bertogna_edf_comp.ResponseTimeIterationEDF

namespace ResponseTimeAnalysisEDF

section ExampleRTA

private def num_cpus : ℕ := 2

private def alpha1 : affinity num_cpus :=
  {⟨0, by unfold num_cpus; omega⟩, ⟨1, by unfold num_cpus; omega⟩}

private def alpha2 : affinity num_cpus :=
  {⟨0, by unfold num_cpus; omega⟩}

private def alpha3 : affinity num_cpus :=
  {⟨1, by unfold num_cpus; omega⟩}

private def tsk1 : concrete_task num_cpus :=
  { task_id := 1, task_cost := 3, task_period := 5, task_deadline := 3, task_affinity := alpha1 }

private def tsk2 : concrete_task num_cpus :=
  { task_id := 2, task_cost := 2, task_period := 6, task_deadline := 5, task_affinity := alpha2 }

private def tsk3 : concrete_task num_cpus :=
  { task_id := 3, task_cost := 2, task_period := 12, task_deadline := 11, task_affinity := alpha3 }

private def ts : List (concrete_task num_cpus) := [tsk1, tsk2, tsk3]

section FactsAboutTaskset

theorem ts_non_empty_affinities :
    ∀ tsk,
      tsk ∈ ts →
      (concrete_task.task_affinity tsk).card > 0 := by
  intro tsk h_mem
  simp [ts, tsk1, tsk2, tsk3] at h_mem
  rcases h_mem with rfl | rfl | rfl <;> decide

theorem ts_has_valid_parameters :
    valid_sporadic_taskset
      (fun t : concrete_task num_cpus => t.task_cost)
      (fun t : concrete_task num_cpus => t.task_period)
      (fun t : concrete_task num_cpus => t.task_deadline) ts := by
  intro tsk h_mem
  simp [ts, tsk1, tsk2, tsk3] at h_mem
  rcases h_mem with rfl | rfl | rfl <;>
    simp [is_valid_sporadic_task, task_cost_positive, task_period_positive,
          task_deadline_positive, task_cost_le_deadline, task_cost_le_period]

theorem ts_has_constrained_deadlines :
    ∀ tsk,
      tsk ∈ ts →
      (concrete_task.task_deadline tsk) ≤ (concrete_task.task_period tsk) := by
  intro tsk h_mem
  simp [ts, tsk1, tsk2, tsk3] at h_mem
  rcases h_mem with rfl | rfl | rfl <;> simp

end FactsAboutTaskset

noncomputable def edf_schedulable
    (task_cost : concrete_task num_cpus → Time)
    (task_period : concrete_task num_cpus → Time)
    (task_deadline : concrete_task num_cpus → Time)
    (n : ℕ)
    (alpha : task_affinity (concrete_task n) n)
    (alpha' : task_affinity (concrete_task n) n)
    (ts : List (concrete_task n)) : Bool :=
  let tc : concrete_task n → Time := fun t => t.task_cost
  let tp : concrete_task n → Time := fun t => t.task_period
  let td : concrete_task n → Time := fun t => t.task_deadline
  let max_jobs' (tsk : concrete_task n) (R_tsk delta : Time) : ℕ :=
    (delta + R_tsk - tc tsk) / (tp tsk)
  let W' (tsk : concrete_task n) (R_tsk delta : Time) : ℕ :=
    let e_k := tc tsk; let p_k := tp tsk
    min e_k (delta + R_tsk - e_k - max_jobs' tsk R_tsk delta * p_k) +
      max_jobs' tsk R_tsk delta * e_k
  let interference_bound_generic' (tsk : concrete_task n) (delta : Time)
      (tsk_R : concrete_task n × Time) : ℕ :=
    min (W' tsk_R.1 tsk_R.2 delta) (delta - tc tsk + 1)
  let edf_specific_bound' (tsk : concrete_task n) (tsk_other : concrete_task n) (R_other delta : Time) : ℕ :=
    let d_tsk := td tsk; let e_other := tc tsk_other
    let p_other := tp tsk_other; let d_other := td tsk_other
    (d_tsk / p_other) * e_other + min e_other (d_tsk % p_other - (d_other - R_other))
  let interference_bound_edf' (tsk : concrete_task n) (delta : Time)
      (tsk_R : concrete_task n × Time) : ℕ :=
    min (interference_bound_generic' tsk delta tsk_R) (edf_specific_bound' tsk tsk_R.1 tsk_R.2 delta)
  let different_task_in' (tsk : concrete_task n) (alpha'_tsk : Finset (Fin n))
      (tsk_other : concrete_task n) : Bool :=
    decide (tsk_other ≠ tsk) && decide ((alpha'_tsk ∩ alpha tsk_other).Nonempty)
  let total_interference' (tsk : concrete_task n) (alpha'_tsk : Finset (Fin n))
      (R_prev : List (concrete_task n × Time)) (delta : Time) : ℕ :=
    (R_prev.filter (fun tsk_R => different_task_in' tsk alpha'_tsk tsk_R.1)).map
      (fun tsk_R => interference_bound_edf' tsk delta tsk_R) |>.sum
  let response_time_bound' (R_prev : List (concrete_task n × Time))
      (tsk : concrete_task n) (delta : Time) : Time :=
    tc tsk + (total_interference' tsk (alpha' tsk) R_prev delta) / (alpha' tsk).card
  let update_bound' (rt_bounds : List (concrete_task n × Time))
      (pair : concrete_task n × Time) : concrete_task n × Time :=
    (pair.1, response_time_bound' rt_bounds pair.1 pair.2)
  let iteration' (rt_bounds : List (concrete_task n × Time)) :
      List (concrete_task n × Time) :=
    rt_bounds.map (update_bound' rt_bounds)
  let initial := ts.map (fun tsk => (tsk, tc tsk))
  let max_steps := (ts.map (fun tsk => td tsk - tc tsk)).sum + 1
  let R_values := iteration'^[max_steps] initial
  let check := R_values.all (fun pair => decide (pair.2 ≤ td pair.1))
  if check then true else false

private noncomputable def schedulability_test : List (concrete_task num_cpus) → Bool :=
  edf_schedulable
    (fun t => t.task_cost) (fun t => t.task_period) (fun t => t.task_deadline)
    num_cpus
    (fun t => t.task_affinity) (fun t => t.task_affinity)

set_option maxRecDepth 100000 in
theorem schedulability_test_succeeds :
    schedulability_test ts = true := by decide

private def arr_seq : arrival_sequence (concrete_job num_cpus) :=
  periodic_arrival_sequence ts

private noncomputable def sched : schedule (concrete_job num_cpus) num_cpus :=
  scheduler
    (fun j : concrete_job num_cpus => j.job_arrival)
    (fun j : concrete_job num_cpus => j.job_cost)
    (fun j : concrete_job num_cpus => j.job_task)
    arr_seq
    (fun t => t.task_affinity)
    (JLFP_to_JLDP (EDF
      (fun j : concrete_job num_cpus => j.job_arrival)
      (fun j : concrete_job num_cpus => j.job_deadline)))

private def no_deadline_missed_by (tsk : concrete_task num_cpus) : Prop :=
  task_misses_no_deadline
    (fun j : concrete_job num_cpus => j.job_arrival)
    (fun j : concrete_job num_cpus => j.job_cost)
    (fun j : concrete_job num_cpus => j.job_deadline)
    (fun j : concrete_job num_cpus => j.job_task)
    arr_seq sched tsk

theorem ts_is_schedulable :
    ∀ tsk,
      tsk ∈ ts →
      no_deadline_missed_by tsk := by
  intro tsk h_mem
  unfold no_deadline_missed_by
  apply Prosa.Classic.Analysis.Apa.Bertogna_edf_comp.ResponseTimeIterationEDF.taskset_schedulable_by_edf_rta
    (task_cost := fun t : concrete_task num_cpus => t.task_cost)
    (task_period := fun t : concrete_task num_cpus => t.task_period)
    (task_deadline := fun t : concrete_task num_cpus => t.task_deadline)
    (job_arrival := fun j : concrete_job num_cpus => j.job_arrival)
    (job_cost := fun j : concrete_job num_cpus => j.job_cost)
    (job_deadline := fun j : concrete_job num_cpus => j.job_deadline)
    (job_task := fun j : concrete_job num_cpus => j.job_task)
    (alpha := fun t => t.task_affinity)
    (alpha' := fun t => t.task_affinity)
    (ts := ts)
    (arr_seq := arr_seq)
    (sched := sched)
  · exact ts_has_valid_parameters
  · exact ts_has_constrained_deadlines
  · exact ts_non_empty_affinities
  · intro tsk' _; intro x hx; exact hx
  · intro j hj; exact periodic_arrivals_all_jobs_from_taskset ts j hj
  · exact periodic_arrivals_valid_job_parameters ts ts_has_valid_parameters
  · exact periodic_arrivals_are_sporadic ts
  · exact scheduler_jobs_come_from_arrival_sequence
      (fun j : concrete_job num_cpus => j.job_arrival)
      (fun j : concrete_job num_cpus => j.job_cost)
      (fun j : concrete_job num_cpus => j.job_task)
      (fun t => t.task_affinity)
      arr_seq
      (JLFP_to_JLDP (EDF
        (fun j : concrete_job num_cpus => j.job_arrival)
        (fun j : concrete_job num_cpus => j.job_deadline)))
  · exact scheduler_jobs_must_arrive_to_execute
      (fun j : concrete_job num_cpus => j.job_arrival)
      (fun j : concrete_job num_cpus => j.job_cost)
      (fun j : concrete_job num_cpus => j.job_task)
      (fun t => t.task_affinity)
      arr_seq
      (JLFP_to_JLDP (EDF
        (fun j : concrete_job num_cpus => j.job_arrival)
        (fun j : concrete_job num_cpus => j.job_deadline)))
  · exact scheduler_completed_jobs_dont_execute
      (fun j : concrete_job num_cpus => j.job_arrival)
      (fun j : concrete_job num_cpus => j.job_cost)
      (fun j : concrete_job num_cpus => j.job_task)
      (fun t => t.task_affinity)
      arr_seq
      (periodic_arrivals_are_consistent ts)
      (periodic_arrivals_is_a_set ts (by decide))
      (JLFP_to_JLDP (EDF
        (fun j : concrete_job num_cpus => j.job_arrival)
        (fun j : concrete_job num_cpus => j.job_deadline)))
  · exact scheduler_sequential_jobs
      (fun j : concrete_job num_cpus => j.job_arrival)
      (fun j : concrete_job num_cpus => j.job_cost)
      (fun j : concrete_job num_cpus => j.job_task)
      (fun t => t.task_affinity)
      arr_seq
      (periodic_arrivals_are_consistent ts)
      (periodic_arrivals_is_a_set ts (by decide))
      (JLFP_to_JLDP (EDF
        (fun j : concrete_job num_cpus => j.job_arrival)
        (fun j : concrete_job num_cpus => j.job_deadline)))
  · exact scheduler_respects_affinity
      (fun j : concrete_job num_cpus => j.job_arrival)
      (fun j : concrete_job num_cpus => j.job_cost)
      (fun j : concrete_job num_cpus => j.job_task)
      (fun t => t.task_affinity)
      arr_seq
      (JLFP_to_JLDP (EDF
        (fun j : concrete_job num_cpus => j.job_arrival)
        (fun j : concrete_job num_cpus => j.job_deadline)))
  · exact scheduler_apa_work_conserving
      (fun j : concrete_job num_cpus => j.job_arrival)
      (fun j : concrete_job num_cpus => j.job_cost)
      (fun j : concrete_job num_cpus => j.job_task)
      (fun t => t.task_affinity)
      arr_seq
      (periodic_arrivals_are_consistent ts)
      (periodic_arrivals_is_a_set ts (by decide))
      (JLFP_to_JLDP (EDF
        (fun j : concrete_job num_cpus => j.job_arrival)
        (fun j : concrete_job num_cpus => j.job_deadline)))
      (fun _ => EDF_is_transitive
        (fun j : concrete_job num_cpus => j.job_arrival)
        (fun j : concrete_job num_cpus => j.job_deadline))
      (fun _ _ _ => by simp only [JLFP_to_JLDP, EDF, decide_eq_true_eq]; exact le_total _ _)
  · exact scheduler_respects_policy
      (fun j : concrete_job num_cpus => j.job_arrival)
      (fun j : concrete_job num_cpus => j.job_cost)
      (fun j : concrete_job num_cpus => j.job_task)
      (fun t => t.task_affinity)
      arr_seq
      (periodic_arrivals_are_consistent ts)
      (periodic_arrivals_is_a_set ts (by decide))
      (JLFP_to_JLDP (EDF
        (fun j : concrete_job num_cpus => j.job_arrival)
        (fun j : concrete_job num_cpus => j.job_deadline)))
      (fun _ => EDF_is_transitive
        (fun j : concrete_job num_cpus => j.job_arrival)
        (fun j : concrete_job num_cpus => j.job_deadline))
      (fun _ _ _ => by simp only [JLFP_to_JLDP, EDF, decide_eq_true_eq]; exact le_total _ _)
  · -- H_test_succeeds: edf_schedulable (analysis Prop version)
    show Prosa.Classic.Analysis.Apa.Bertogna_edf_comp.ResponseTimeIterationEDF.edf_schedulable
      (fun t : concrete_task num_cpus => t.task_cost)
      (fun t : concrete_task num_cpus => t.task_period)
      (fun t : concrete_task num_cpus => t.task_deadline)
      (fun t => t.task_affinity) (fun t => t.task_affinity) ts
    native_decide
  · exact h_mem

end ExampleRTA

end ResponseTimeAnalysisEDF

end Prosa.Classic.Implementation.Apa.Bertogna_edf_example
