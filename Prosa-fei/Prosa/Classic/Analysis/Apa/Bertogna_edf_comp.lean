-- Translated from: ../rt-proofs/classic/analysis/apa/bertogna_edf_comp.v
import Prosa.Classic.Util.All
import Prosa.Classic.Analysis.Apa.Bertogna_edf_theory
import Mathlib.Tactic

set_option autoImplicit false

namespace Prosa.Classic.Analysis.Apa.Bertogna_edf_comp

open Prosa.Classic.Model.Time
open Prosa.Classic.Model.Arrival.Basic.Arrival_sequence
open Prosa.Classic.Model.Arrival.Basic.Job
open Prosa.Classic.Model.Arrival.Basic.Task
open Prosa.Classic.Model.Arrival.Basic.Task.SporadicTask
open Prosa.Classic.Model.Arrival.Basic.Task.SporadicTaskset
open Prosa.Classic.Model.Arrival.Basic.Task_arrival
open Prosa.Classic.Model.Schedule.Global.Basic.Schedule
open Prosa.Classic.Model.Schedule.Global.Basic.Schedule.Schedule
open Prosa.Classic.Model.Schedule.Global.Basic.Schedule.ScheduleOfSporadicTask
open Prosa.Classic.Model.Schedule.Global.Response_time.ResponseTime
open Prosa.Classic.Model.Schedule.Global.Schedulability.Schedulability
open Prosa.Classic.Model.Schedule.Apa.Platform
open Prosa.Classic.Model.Schedule.Apa.Interference
open Prosa.Classic.Model.Schedule.Apa.Affinity
open Prosa.Classic.Model.Schedule.Apa.Constrained_deadlines hiding apa_work_conserving respects_FP_policy_under_weak_APA
open Prosa.Classic.Model.Priority
open Prosa.Classic.Analysis.Apa.Bertogna_edf_theory.ResponseTimeAnalysisEDF
open Prosa.Classic.Analysis.Apa.Workload_bound.WorkloadBound
open Prosa.Classic.Analysis.Apa.Interference_bound.InterferenceBoundGeneric
open Prosa.Util.Div_mod
open Prosa.Classic.Util.Fixedpoint

namespace ResponseTimeIterationEDF

section Analysis

variable {sporadic_task : Type _} [DecidableEq sporadic_task]
variable (task_cost : sporadic_task → Time)
variable (task_period : sporadic_task → Time)
variable (task_deadline : sporadic_task → Time)

variable {Job : Type _} [DecidableEq Job]
variable (job_arrival : Job → Time)
variable (job_cost : Job → Time)
variable (job_deadline : Job → Time)
variable (job_task : Job → sporadic_task)

abbrev task_with_response_time (sporadic_task : Type _) := (sporadic_task × Time)

variable {num_cpus : ℕ}
variable (alpha : task_affinity sporadic_task num_cpus)
variable (alpha' : task_affinity sporadic_task num_cpus)

private abbrev I (rt_bounds : List (sporadic_task × Time))
    (tsk : sporadic_task) (delta : Time) : ℕ :=
  total_interference_bound_edf task_cost task_period task_deadline alpha tsk
    (alpha' tsk) rt_bounds delta

def edf_response_time_bound (rt_bounds : List (sporadic_task × Time))
    (tsk : sporadic_task) (delta : Time) : Time :=
  task_cost tsk + div_floor
    (total_interference_bound_edf task_cost task_period task_deadline alpha tsk
      (alpha' tsk) rt_bounds delta)
    (alpha' tsk).card

def R_le_deadline (pair : sporadic_task × Time) : Bool :=
  decide (pair.2 ≤ task_deadline pair.1)

def update_bound (rt_bounds : List (sporadic_task × Time))
    (pair : sporadic_task × Time) : sporadic_task × Time :=
  (pair.1, edf_response_time_bound task_cost task_period task_deadline alpha alpha' rt_bounds pair.1 pair.2)

private def initial_state (ts : List sporadic_task) : List (sporadic_task × Time) :=
  ts.map (fun tsk => (tsk, task_cost tsk))

def edf_rta_iteration (rt_bounds : List (sporadic_task × Time)) :
    List (sporadic_task × Time) :=
  rt_bounds.map (update_bound task_cost task_period task_deadline alpha alpha' rt_bounds)

private def max_steps (ts : List sporadic_task) : ℕ :=
  (ts.map (fun tsk => task_deadline tsk - task_cost tsk)).sum + 1

def edf_claimed_bounds (ts : List sporadic_task) :
    Option (List (sporadic_task × Time)) :=
  let R_values := (edf_rta_iteration task_cost task_period task_deadline alpha alpha')^[max_steps task_deadline task_cost ts]
                    (initial_state task_cost ts)
  if R_values.all (R_le_deadline task_deadline) then
    some R_values
  else none

def edf_schedulable (ts : List sporadic_task) : Prop :=
  edf_claimed_bounds task_cost task_period task_deadline alpha alpha' ts ≠ none

instance decidable_edf_schedulable (ts : List sporadic_task) :
    Decidable (edf_schedulable task_cost task_period task_deadline alpha alpha' ts) :=
  inferInstanceAs (Decidable (_ ≠ none))

section SimpleLemmas

theorem edf_claimed_bounds_unzip1_update_bound :
    ∀ (l rt_bounds : List (sporadic_task × Time)),
      (l.map (update_bound task_cost task_period task_deadline alpha alpha' rt_bounds)).map Prod.fst =
        l.map Prod.fst := by sorry

theorem edf_claimed_bounds_unzip1_iteration :
    ∀ (l : List sporadic_task) (k : ℕ),
      ((edf_rta_iteration task_cost task_period task_deadline alpha alpha')^[k]
        (initial_state task_cost l)).map Prod.fst = l := by sorry

theorem edf_claimed_bounds_size :
    ∀ (l : List sporadic_task) (k : ℕ),
      ((edf_rta_iteration task_cost task_period task_deadline alpha alpha')^[k]
        (initial_state task_cost l)).length = l.length := by sorry

theorem edf_claimed_bounds_ge_cost :
    ∀ (l : List sporadic_task) (k : ℕ) (tsk : sporadic_task) (R : Time),
      (tsk, R) ∈ (edf_rta_iteration task_cost task_period task_deadline alpha alpha')^[k]
        (initial_state task_cost l) →
      R ≥ task_cost tsk := by sorry

theorem edf_claimed_bounds_le_deadline :
    ∀ (ts : List sporadic_task) (rt_bounds : List (sporadic_task × Time))
      (tsk : sporadic_task) (R : Time),
      edf_claimed_bounds task_cost task_period task_deadline alpha alpha' ts = some rt_bounds →
      (tsk, R) ∈ rt_bounds →
      R ≤ task_deadline tsk := by sorry

theorem edf_claimed_bounds_has_R_for_every_task :
    ∀ (ts : List sporadic_task) (rt_bounds : List (sporadic_task × Time))
      (tsk : sporadic_task),
      edf_claimed_bounds task_cost task_period task_deadline alpha alpha' ts = some rt_bounds →
      tsk ∈ ts →
      ∃ R, (tsk, R) ∈ rt_bounds := by sorry

end SimpleLemmas

section Convergence

variable (ts : List sporadic_task)
variable (H_valid_task_parameters :
  valid_sporadic_taskset task_cost task_period task_deadline ts)

private abbrev f (k : ℕ) : List (sporadic_task × Time) :=
  (edf_rta_iteration task_cost task_period task_deadline alpha alpha')^[k]
    (initial_state task_cost ts)

private def all_le (l1 l2 : List (sporadic_task × Time)) : Prop :=
  l1.map Prod.fst = l2.map Prod.fst ∧
  ∀ p, p ∈ l1.zip l2 → p.1.2 ≤ p.2.2

private def one_lt (l1 l2 : List (sporadic_task × Time)) : Prop :=
  l1.map Prod.fst = l2.map Prod.fst ∧
  ∃ p, p ∈ l1.zip l2 ∧ p.1.2 < p.2.2

section RelationProperties

theorem all_le_reflexive :
    ∀ l : List (sporadic_task × Time),
      all_le l l := by sorry

theorem all_le_transitive :
    ∀ x y z : List (sporadic_task × Time),
      all_le x y → all_le y z → all_le x z := by sorry

include H_valid_task_parameters in
theorem bertogna_edf_comp_iteration_preserves_minimum :
    ∀ step,
      all_le (initial_state task_cost ts)
        (f task_cost task_period task_deadline alpha alpha' ts step) := by sorry

include H_valid_task_parameters in
theorem bertogna_edf_comp_iteration_inductive (P : List (sporadic_task × Time) → Prop) :
    P (initial_state task_cost ts) →
    (∀ k, P (f task_cost task_period task_deadline alpha alpha' ts k) →
      P (f task_cost task_period task_deadline alpha alpha' ts (k + 1))) →
    P (f task_cost task_period task_deadline alpha alpha' ts (max_steps task_deadline task_cost ts)) := by sorry

include H_valid_task_parameters in
theorem bertogna_edf_comp_iteration_preserves_order :
    ∀ l1 l2 : List (sporadic_task × Time),
      all_le (initial_state task_cost ts) l1 →
      all_le l1 l2 →
      all_le (edf_rta_iteration task_cost task_period task_deadline alpha alpha' l1)
        (edf_rta_iteration task_cost task_period task_deadline alpha alpha' l2) := by sorry

include H_valid_task_parameters in
theorem bertogna_edf_comp_iteration_monotonic :
    ∀ k, all_le (f task_cost task_period task_deadline alpha alpha' ts k)
      (f task_cost task_period task_deadline alpha alpha' ts (k + 1)) := by sorry

end RelationProperties

theorem bertogna_edf_comp_f_converges_with_no_tasks :
    ts.length = 0 →
    f task_cost task_period task_deadline alpha alpha' ts (max_steps task_deadline task_cost ts) =
      f task_cost task_period task_deadline alpha alpha' ts (max_steps task_deadline task_cost ts + 1) := by sorry

theorem bertogna_edf_comp_f_converges_early :
    (∃ k, k ≤ max_steps task_deadline task_cost ts ∧
      f task_cost task_period task_deadline alpha alpha' ts k =
        f task_cost task_period task_deadline alpha alpha' ts (k + 1)) →
    f task_cost task_period task_deadline alpha alpha' ts (max_steps task_deadline task_cost ts) =
      f task_cost task_period task_deadline alpha alpha' ts (max_steps task_deadline task_cost ts + 1) := by sorry

section DerivingContradiction

variable (H_at_least_one_task : ts.length > 0)
variable (H_keeps_diverging :
  ∀ k, k ≤ max_steps task_deadline task_cost ts →
    f task_cost task_period task_deadline alpha alpha' ts k ≠
      f task_cost task_period task_deadline alpha alpha' ts (k + 1))

include H_valid_task_parameters H_at_least_one_task H_keeps_diverging in
theorem bertogna_edf_comp_f_increases :
    ∀ k, k ≤ max_steps task_deadline task_cost ts →
      one_lt (f task_cost task_period task_deadline alpha alpha' ts k)
        (f task_cost task_period task_deadline alpha alpha' ts (k + 1)) := by sorry

include H_valid_task_parameters H_at_least_one_task H_keeps_diverging in
theorem bertogna_edf_comp_rt_grows_too_much :
    ∀ k, k ≤ max_steps task_deadline task_cost ts →
      ((f task_cost task_period task_deadline alpha alpha' ts k).map
        (fun p => p.2 - task_cost p.1)).sum + 1 > k := by sorry

end DerivingContradiction

include H_valid_task_parameters in
theorem edf_claimed_bounds_finds_fixed_point_of_list :
    ∀ rt_bounds : List (sporadic_task × Time),
      edf_claimed_bounds task_cost task_period task_deadline alpha alpha' ts = some rt_bounds →
      valid_sporadic_taskset task_cost task_period task_deadline ts →
      f task_cost task_period task_deadline alpha alpha' ts (max_steps task_deadline task_cost ts) =
        edf_rta_iteration task_cost task_period task_deadline alpha alpha'
          (f task_cost task_period task_deadline alpha alpha' ts (max_steps task_deadline task_cost ts)) := by sorry

include H_valid_task_parameters in
theorem edf_claimed_bounds_finds_least_fixed_point :
    ∀ v : List (sporadic_task × Time),
      all_le (initial_state task_cost ts) v →
      v = edf_rta_iteration task_cost task_period task_deadline alpha alpha' v →
      all_le (f task_cost task_period task_deadline alpha alpha' ts (max_steps task_deadline task_cost ts)) v := by sorry

include H_valid_task_parameters in
theorem edf_claimed_bounds_finds_fixed_point_for_each_bound :
    ∀ (tsk : sporadic_task) (R : Time) (rt_bounds : List (sporadic_task × Time)),
      edf_claimed_bounds task_cost task_period task_deadline alpha alpha' ts = some rt_bounds →
      (tsk, R) ∈ rt_bounds →
      R = edf_response_time_bound task_cost task_period task_deadline alpha alpha' rt_bounds tsk R := by sorry

end Convergence

section MainProof

variable (ts : List sporadic_task)

variable (H_valid_task_parameters :
  valid_sporadic_taskset task_cost task_period task_deadline ts)

variable (H_constrained_deadlines :
  ∀ tsk, tsk ∈ ts → task_deadline tsk ≤ task_period tsk)

variable (H_non_empty_affinity :
  ∀ tsk, tsk ∈ ts → (alpha' tsk).card > 0)

variable (H_subaffinity :
  ∀ tsk, tsk ∈ ts → is_subaffinity (alpha' tsk) (alpha tsk))

variable (arr_seq : arrival_sequence Job)

variable (H_all_jobs_from_taskset :
  ∀ j, arrives_in arr_seq j → job_task j ∈ ts)

variable (H_valid_job_parameters :
  ∀ j,
    arrives_in arr_seq j →
    valid_sporadic_job task_cost task_deadline job_cost job_deadline job_task j)

variable (H_sporadic_tasks :
  sporadic_task_model task_period job_arrival job_task arr_seq)

variable (sched : schedule Job num_cpus)
variable (H_jobs_come_from_arrival_sequence :
  jobs_come_from_arrival_sequence sched arr_seq)

variable (H_jobs_must_arrive_to_execute :
  jobs_must_arrive_to_execute job_arrival sched)
variable (H_completed_jobs_dont_execute :
  completed_jobs_dont_execute job_cost sched)

variable (H_sequential_jobs : sequential_jobs sched)

variable (H_respects_affinity : respects_affinity job_task sched alpha)
variable (H_work_conserving :
  apa_work_conserving job_arrival job_cost job_task arr_seq sched alpha)
variable (H_edf_policy :
  respects_JLFP_policy_under_weak_APA job_arrival job_cost job_task arr_seq
    sched alpha (EDF job_arrival job_deadline))

def no_deadline_missed_by_task (tsk : sporadic_task) :=
  task_misses_no_deadline job_arrival job_cost job_deadline job_task arr_seq sched tsk

def no_deadline_missed_by_job :=
  job_misses_no_deadline job_arrival job_cost job_deadline sched

private abbrev response_time_bounded_by_main (tsk : sporadic_task) (R : Time) :=
  is_response_time_bound_of_task job_arrival job_cost job_task arr_seq sched tsk R

include H_valid_task_parameters H_constrained_deadlines
  H_non_empty_affinity H_subaffinity
  H_all_jobs_from_taskset H_valid_job_parameters
  H_sporadic_tasks
  H_jobs_come_from_arrival_sequence
  H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
  H_sequential_jobs
  H_respects_affinity H_work_conserving H_edf_policy in
theorem edf_analysis_yields_response_time_bounds :
    ∀ (tsk : sporadic_task) (R : Time),
      (match edf_claimed_bounds task_cost task_period task_deadline alpha alpha' ts with
       | some rt_bounds => (tsk, R) ∈ rt_bounds
       | none => False) →
      response_time_bounded_by_main job_arrival job_cost job_task arr_seq sched tsk R := by sorry

variable (H_test_succeeds :
  edf_schedulable task_cost task_period task_deadline alpha alpha' ts)

include H_valid_task_parameters H_constrained_deadlines
  H_non_empty_affinity H_subaffinity
  H_all_jobs_from_taskset H_valid_job_parameters
  H_sporadic_tasks
  H_jobs_come_from_arrival_sequence
  H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
  H_sequential_jobs
  H_respects_affinity H_work_conserving H_edf_policy H_test_succeeds in
theorem taskset_schedulable_by_edf_rta :
    ∀ tsk, tsk ∈ ts →
      no_deadline_missed_by_task job_arrival job_cost job_deadline job_task arr_seq sched tsk := by sorry

include H_valid_task_parameters H_constrained_deadlines
  H_non_empty_affinity H_subaffinity
  H_all_jobs_from_taskset H_valid_job_parameters
  H_sporadic_tasks
  H_jobs_come_from_arrival_sequence
  H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
  H_sequential_jobs
  H_respects_affinity H_work_conserving H_edf_policy H_test_succeeds in
theorem jobs_schedulable_by_edf_rta :
    ∀ j, arrives_in arr_seq j →
      no_deadline_missed_by_job job_arrival job_cost job_deadline sched j := by sorry

end MainProof

end Analysis

end ResponseTimeIterationEDF

end Prosa.Classic.Analysis.Apa.Bertogna_edf_comp
