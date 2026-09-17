-- Translated from: ../rt-proofs/classic/analysis/global/jitter/bertogna_fp_theory.v
import Prosa.Classic.Util.All
import Prosa.Classic.Model.Arrival.Basic.Task
import Prosa.Classic.Model.Schedule.Global.Workload
import Prosa.Classic.Model.Schedule.Global.Jitter.Job
import Prosa.Classic.Analysis.Global.Jitter.Workload_bound
import Prosa.Classic.Model.Priority
import Prosa.Classic.Model.Arrival.Basic.Task_arrival
import Prosa.Classic.Model.Schedule.Global.Basic.Schedule
import Prosa.Classic.Model.Schedule.Global.Basic.Interference
import Prosa.Classic.Model.Schedule.Global.Response_time
import Prosa.Classic.Model.Schedule.Global.Schedulability
import Prosa.Classic.Model.Schedule.Global.Jitter.Schedule
import Prosa.Classic.Model.Schedule.Global.Jitter.Constrained_deadlines
import Prosa.Classic.Util.Div_mod
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

set_option autoImplicit false

namespace Prosa.Classic.Analysis.Global.Jitter.Bertogna_fp_theory

open Classical
open Prosa.Classic.Model.Time
open Prosa.Classic.Model.Arrival.Basic.Task
open Prosa.Classic.Model.Arrival.Basic.Task.SporadicTask
open Prosa.Classic.Model.Arrival.Basic.Task.SporadicTaskset
open Prosa.Classic.Model.Arrival.Basic.Arrival_sequence
open Prosa.Classic.Model.Schedule.Global.Basic.Schedule
open Prosa.Classic.Model.Schedule.Global.Basic.Schedule.Schedule
open Prosa.Classic.Model.Schedule.Global.Basic.Schedule.ScheduleOfSporadicTask
open Prosa.Classic.Model.Schedule.Global.Workload
open Prosa.Classic.Model.Schedule.Global.Response_time
open Prosa.Classic.Model.Schedule.Global.Response_time.ResponseTime
open Prosa.Classic.Model.Schedule.Global.Schedulability
open Prosa.Classic.Model.Schedule.Global.Schedulability.Schedulability
open Prosa.Classic.Model.Schedule.Global.Jitter.Job
open Prosa.Classic.Model.Schedule.Global.Jitter.Schedule
open Prosa.Classic.Model.Schedule.Global.Jitter.Schedule.ScheduleWithJitter
open Prosa.Classic.Model.Schedule.Global.Jitter.Schedule.ScheduleOfSporadicTaskWithJitter
open Prosa.Classic.Model.Schedule.Global.Jitter.Constrained_deadlines
open Prosa.Classic.Model.Priority
open Prosa.Classic.Analysis.Global.Jitter.Workload_bound
open Prosa.Classic.Analysis.Global.Jitter.Workload_bound.WorkloadBoundJitter
open Prosa.Util.Div_mod

namespace ResponseTimeAnalysisFP

section InterferenceBoundFP

variable {sporadic_task : Type _} [DecidableEq sporadic_task]
variable (task_cost : sporadic_task → Time)
variable (task_period : sporadic_task → Time)
variable (task_jitter : sporadic_task → Time)
variable (tsk : sporadic_task)
variable (hp_bounds : List (sporadic_task × Time))
variable (delta : Time)

noncomputable def interference_bound_generic (tsk_R : sporadic_task × Time) : ℕ :=
  min (W_jitter task_cost task_period task_jitter tsk_R.1 tsk_R.2 delta)
      (delta - task_cost tsk + 1)

noncomputable def total_interference_bound_fp : ℕ :=
  (hp_bounds.map (interference_bound_generic task_cost task_period task_jitter tsk delta)).sum

end InterferenceBoundFP

section JitterInterference

variable {sporadic_task : Type _} [DecidableEq sporadic_task]
variable {Job : Type _} [DecidableEq Job]
variable (job_arrival : Job → Time)
variable (job_cost : Job → Time)
variable (job_task : Job → sporadic_task)
variable (job_jitter : Job → Time)
variable {num_cpus : ℕ}
variable (sched : schedule Job num_cpus)
variable (j : Job)

noncomputable def total_interference (t1 t2 : Time) : ℕ :=
  ∑ t ∈ Finset.Ico t1 t2,
    if ScheduleWithJitter.backlogged job_arrival job_cost job_jitter sched j t then 1 else 0

noncomputable def task_interference (tsk_other : sporadic_task) (t1 t2 : Time) : ℕ :=
  ∑ t ∈ Finset.Ico t1 t2,
    ∑ cpu : Fin num_cpus,
      if ScheduleWithJitter.backlogged job_arrival job_cost job_jitter sched j t ∧
         ScheduleOfSporadicTaskWithJitter.task_scheduled_on job_task sched tsk_other cpu t = true
      then 1 else 0

end JitterInterference

section ResponseTimeBound

variable {sporadic_task : Type _} [DecidableEq sporadic_task]
variable (task_cost : sporadic_task → Time)
variable (task_period : sporadic_task → Time)
variable (task_deadline : sporadic_task → Time)
variable (task_jitter : sporadic_task → Time)

variable {Job : Type _} [DecidableEq Job]
variable (job_arrival : Job → Time)
variable (job_cost : Job → Time)
variable (job_deadline : Job → Time)
variable (job_task : Job → sporadic_task)
variable (job_jitter : Job → Time)

variable {arr_seq : arrival_sequence Job}

variable (H_sporadic_tasks :
  Prosa.Classic.Model.Arrival.Basic.Task_arrival.sporadic_task_model task_period job_arrival job_task arr_seq)
variable (H_valid_job_parameters :
  ∀ j,
    arrives_in arr_seq j →
    valid_sporadic_job_with_jitter task_cost task_deadline task_jitter job_cost
                                   job_deadline job_task job_jitter j)

variable (ts : List sporadic_task)
variable (H_valid_task_parameters :
  valid_sporadic_taskset task_cost task_period task_deadline ts)
variable (H_constrained_deadlines :
  ∀ tsk, tsk ∈ ts → task_deadline tsk ≤ task_period tsk)

variable (H_all_jobs_from_taskset :
  ∀ j,
    arrives_in arr_seq j → job_task j ∈ ts)

variable {num_cpus : ℕ}
variable (sched : schedule Job num_cpus)
variable (H_jobs_come_from_arrival_sequence :
  jobs_come_from_arrival_sequence sched arr_seq)

variable (H_sequential_jobs : sequential_jobs sched)
variable (H_jobs_execute_after_jitter :
  Prosa.Classic.Model.Schedule.Global.Jitter.Schedule.ScheduleWithJitter.jobs_execute_after_jitter
    job_arrival job_jitter sched)
variable (H_completed_jobs_dont_execute :
  completed_jobs_dont_execute job_cost sched)

variable (H_at_least_one_cpu : num_cpus > 0)

variable (higher_eq_priority : FP_policy sporadic_task)

variable (H_work_conserving :
  Prosa.Classic.Model.Schedule.Global.Jitter.Constrained_deadlines.work_conserving
    job_arrival job_cost job_jitter arr_seq sched)
variable (H_respects_priority :
  respects_FP_policy_jitter job_arrival job_cost job_task job_jitter arr_seq sched higher_eq_priority)

noncomputable def no_deadline_is_missed_by_tsk (tsk : sporadic_task) : Prop :=
  task_misses_no_deadline job_arrival job_cost job_deadline job_task arr_seq sched tsk

def response_time_bounded_by (tsk : sporadic_task) (R : Time) : Prop :=
  is_response_time_bound_of_task job_arrival job_cost job_task arr_seq sched tsk R

variable (tsk : sporadic_task)
variable (task_in_ts : tsk ∈ ts)

variable (hp_bounds : List (sporadic_task × Time))
variable (H_response_time_of_interfering_tasks_is_known :
  ∀ hp_tsk R,
    (hp_tsk, R) ∈ hp_bounds →
    is_response_time_bound_of_task job_arrival job_cost job_task arr_seq sched hp_tsk (task_jitter hp_tsk + R))

variable (H_hp_bounds_has_interfering_tasks :
  ∀ hp_tsk,
    hp_tsk ∈ ts →
    higher_priority_task higher_eq_priority tsk hp_tsk = true →
    ∃ R, (hp_tsk, R) ∈ hp_bounds)

variable (H_response_time_bounds_ge_cost :
  ∀ hp_tsk R,
    (hp_tsk, R) ∈ hp_bounds → R ≥ task_cost hp_tsk)

variable (H_interfering_tasks_miss_no_deadlines :
  ∀ hp_tsk R,
    (hp_tsk, R) ∈ hp_bounds →
    task_jitter hp_tsk + R ≤ task_deadline hp_tsk)

variable (R : Time)
variable (H_response_time_recurrence_holds :
  R = task_cost tsk +
      div_floor
        (total_interference_bound_fp task_cost task_period task_jitter
                                     tsk hp_bounds R)
        num_cpus)

variable (H_response_time_no_larger_than_deadline :
  task_jitter tsk + R ≤ task_deadline tsk)

section Lemmas

variable (j : Job)
variable (H_job_arrives : arrives_in arr_seq j)
variable (H_job_of_tsk : job_task j = tsk)

variable (H_j_not_completed :
  ¬ completed job_cost sched j (job_arrival j + job_jitter j + R))
variable (H_previous_jobs_of_tsk_completed :
  ∀ j0,
    arrives_in arr_seq j0 →
    job_task j0 = tsk →
    job_arrival j0 < job_arrival j →
    completed job_cost sched j0 (job_arrival j0 + task_jitter tsk + R))

section LemmasAboutHPTasks

variable (tsk_other : sporadic_task)
variable (R_other : Time)
variable (H_response_time_of_tsk_other : (tsk_other, R_other) ∈ hp_bounds)

include H_sporadic_tasks H_valid_job_parameters H_valid_task_parameters
  H_constrained_deadlines H_all_jobs_from_taskset H_jobs_come_from_arrival_sequence
  H_sequential_jobs H_jobs_execute_after_jitter H_completed_jobs_dont_execute
  H_response_time_of_interfering_tasks_is_known H_response_time_bounds_ge_cost
  H_interfering_tasks_miss_no_deadlines H_job_arrives H_job_of_tsk
  H_j_not_completed H_previous_jobs_of_tsk_completed
  H_response_time_of_tsk_other

theorem bertogna_fp_workload_bounds_interference :
    task_interference job_arrival job_cost job_task job_jitter sched j tsk_other
      (job_arrival j + job_jitter j) (job_arrival j + job_jitter j + R) ≤
    W_jitter task_cost task_period task_jitter tsk_other R_other R := by
  sorry

end LemmasAboutHPTasks

section DerivingContradiction

include H_sporadic_tasks H_valid_job_parameters H_valid_task_parameters
  H_constrained_deadlines H_all_jobs_from_taskset H_jobs_come_from_arrival_sequence
  H_sequential_jobs H_jobs_execute_after_jitter H_completed_jobs_dont_execute
  H_at_least_one_cpu H_work_conserving H_respects_priority
  task_in_ts H_response_time_of_interfering_tasks_is_known
  H_hp_bounds_has_interfering_tasks H_response_time_bounds_ge_cost
  H_interfering_tasks_miss_no_deadlines H_response_time_recurrence_holds
  H_response_time_no_larger_than_deadline
  H_job_arrives H_job_of_tsk
  H_j_not_completed H_previous_jobs_of_tsk_completed

theorem bertogna_fp_too_much_interference :
    total_interference job_arrival job_cost job_jitter sched j
      (job_arrival j + job_jitter j) (job_arrival j + job_jitter j + R) ≥
    R - task_cost tsk + 1 := by
  set a := job_arrival j + job_jitter j with a_def
  set X := total_interference job_arrival job_cost job_jitter sched j a (a + R)
  -- Bound: cost j ≤ task_cost tsk
  have hCostLe : job_cost j ≤ task_cost tsk := by
    have hVJP := H_valid_job_parameters j H_job_arrives
    have hcost := hVJP.1.2.1
    -- valid_sporadic_job_with_jitter → job_cost_le_task_cost
    unfold Model.Arrival.Basic.Job.job_cost_le_task_cost at hcost
    rw [H_job_of_tsk] at hcost
    exact hcost
  -- Service at a+R is < job_cost j (since j not completed there)
  have hServLt : service sched j (a + R) < job_cost j := by
    by_contra hge; push_neg at hge
    exact H_j_not_completed hge
  -- Per-slot inequality: 1 ≤ backlogged_indicator + service_at
  have hSlot : ∀ t ∈ Finset.Ico a (a + R),
      (1 : ℕ) ≤ (if ScheduleWithJitter.backlogged job_arrival job_cost job_jitter sched j t
                  then 1 else 0) + service_at sched j t := by
    intro t ht
    rw [Finset.mem_Ico] at ht
    by_cases hback : ScheduleWithJitter.backlogged job_arrival job_cost job_jitter sched j t
    · simp [hback]
    · simp only [hback, if_false, zero_add]
      -- Not backlogged: either jitter not passed, not pending, or scheduled
      unfold ScheduleWithJitter.backlogged ScheduleWithJitter.pending at hback
      push_neg at hback
      -- jitter_has_passed since t ≥ a = arr + jit
      have hJitPassed : ScheduleWithJitter.jitter_has_passed job_arrival job_jitter j t := ht.1
      by_cases hSched : scheduled sched j t
      · rcases hSched with ⟨cpu, hOn⟩
        unfold service_at
        calc (1 : ℕ)
            = (if scheduled_on sched j cpu t = true then 1 else 0) := by simp [hOn]
          _ ≤ ∑ cpu' : Fin num_cpus,
                (if scheduled_on sched j cpu' t = true then 1 else 0) :=
              Finset.single_le_sum
                (f := fun c => if scheduled_on sched j c t = true then 1 else 0)
                (fun _ _ => Nat.zero_le _)
                (Finset.mem_univ cpu)
      · -- Not scheduled and not backlogged: hence completed
        have hNotPending : ¬ ScheduleWithJitter.pending job_arrival job_cost job_jitter sched j t := by
          intro hP; exact hSched (hback hP)
        unfold ScheduleWithJitter.pending at hNotPending
        push_neg at hNotPending
        have hCompT : completed job_cost sched j t := hNotPending hJitPassed
        have hCompR : completed job_cost sched j (a + R) :=
          completion_monotonic job_cost sched j H_completed_jobs_dont_execute
            t (a + R) (le_of_lt ht.2) hCompT
        exact absurd hCompR H_j_not_completed
  -- Sum up the per-slot bound
  have hCardR : (Finset.Ico a (a + R)).card = R := by
    rw [Nat.card_Ico]; omega
  have hSum : R ≤ X + ∑ t ∈ Finset.Ico a (a + R), service_at sched j t := by
    have h1 : ∑ _t ∈ Finset.Ico a (a + R), (1 : ℕ) ≤
        ∑ t ∈ Finset.Ico a (a + R),
          ((if ScheduleWithJitter.backlogged job_arrival job_cost job_jitter sched j t
            then 1 else 0) + service_at sched j t) :=
      Finset.sum_le_sum hSlot
    rw [Finset.sum_const, Nat.smul_one_eq_cast, hCardR] at h1
    simp only [Nat.cast_id] at h1
    rw [Finset.sum_add_distrib] at h1
    exact h1
  -- service_during(a, a+R) = service(a+R) since service before a = 0
  have hServEq : ∑ t ∈ Finset.Ico a (a + R), service_at sched j t =
      service sched j (a + R) := by
    unfold service
    -- service(a+R) = ∑ t ∈ Ico 0 (a+R), service_at = ∑ t ∈ Ico 0 a + ∑ t ∈ Ico a (a+R)
    rw [show (a + R) = a + R from rfl]
    rw [← Finset.sum_Ico_consecutive (fun t => service_at sched j t)
        (Nat.zero_le a) (Nat.le_add_right a R)]
    -- ∑ t ∈ Ico 0 a, service_at = 0 (before jitter)
    have hZero : ∑ t ∈ Finset.Ico 0 a, service_at sched j t = 0 :=
      ScheduleWithJitter.cumulative_service_before_jitter_zero
        job_arrival job_jitter sched H_jobs_execute_after_jitter j 0 a (le_refl _)
    rw [hZero, Nat.zero_add]
  rw [hServEq] at hSum
  -- R ≤ task_cost tsk follows from recurrence
  have hCostLeR : task_cost tsk ≤ R := by
    rw [H_response_time_recurrence_holds]; exact Nat.le_add_right _ _
  -- Derive: R - task_cost tsk + 1 ≤ X
  have hStep : R + 1 ≤ X + task_cost tsk :=
    calc R + 1
        ≤ (X + service sched j (a + R)) + 1 := Nat.add_le_add_right hSum 1
      _ = X + (service sched j (a + R) + 1) := (Nat.add_assoc _ _ _)
      _ ≤ X + job_cost j := Nat.add_le_add_left hServLt X
      _ ≤ X + task_cost tsk := Nat.add_le_add_left hCostLe X
  have hCancel : (R - task_cost tsk) + task_cost tsk = R := Nat.sub_add_cancel hCostLeR
  have hStep' : (R - task_cost tsk + 1) + task_cost tsk ≤ X + task_cost tsk := by
    have : (R - task_cost tsk + 1) + task_cost tsk = R + 1 := by
      rw [Nat.add_right_comm]; rw [hCancel]
    rw [this]; exact hStep
  exact Nat.le_of_add_le_add_right hStep'

theorem bertogna_fp_interference_by_different_tasks :
    ∀ t j_other,
      job_arrival j + job_jitter j ≤ t ∧ t < job_arrival j + job_jitter j + R →
      arrives_in arr_seq j_other →
      ScheduleWithJitter.backlogged job_arrival job_cost job_jitter sched j t →
      scheduled sched j_other t →
      job_task j_other ≠ tsk := by
  sorry

theorem bertogna_fp_all_cpus_are_busy :
    ∀ t,
      job_arrival j + job_jitter j ≤ t ∧ t < job_arrival j + job_jitter j + R →
      ScheduleWithJitter.backlogged job_arrival job_cost job_jitter sched j t →
      ts.countP (fun tsk_other =>
        Prosa.Classic.Model.Schedule.Global.Jitter.Constrained_deadlines.task_is_scheduled
          job_task sched tsk_other t &&
        higher_priority_task higher_eq_priority tsk tsk_other) = num_cpus := by
  sorry

theorem bertogna_fp_interference_on_all_cpus :
    ((ts.filter (fun tsk_other => higher_priority_task higher_eq_priority tsk tsk_other)).map
      (fun tsk_k => task_interference job_arrival job_cost job_task job_jitter sched j tsk_k
        (job_arrival j + job_jitter j) (job_arrival j + job_jitter j + R))).sum =
    total_interference job_arrival job_cost job_jitter sched j
      (job_arrival j + job_jitter j) (job_arrival j + job_jitter j + R) * num_cpus := by
  sorry

theorem bertogna_fp_interference_in_non_full_processors :
    ∀ (delta : ℕ),
      let hp_tasks := ts.filter (fun tsk_other => higher_priority_task higher_eq_priority tsk tsk_other)
      let x_val := fun tsk_k => task_interference job_arrival job_cost job_task job_jitter sched j tsk_k
        (job_arrival j + job_jitter j) (job_arrival j + job_jitter j + R)
      let num_exceeding := hp_tasks.countP (fun i => decide (x_val i ≥ delta))
      0 < num_exceeding ∧ num_exceeding < num_cpus →
      ((hp_tasks.filter (fun i => decide (x_val i < delta))).map x_val).sum ≥
        delta * (num_cpus - num_exceeding) := by
  sorry

theorem bertogna_fp_minimum_exceeds_interference :
    ∀ (delta : ℕ),
      let hp_tasks := ts.filter (fun tsk_other => higher_priority_task higher_eq_priority tsk tsk_other)
      let x_val := fun tsk_k => task_interference job_arrival job_cost job_task job_jitter sched j tsk_k
        (job_arrival j + job_jitter j) (job_arrival j + job_jitter j + R)
      (hp_tasks.map x_val).sum ≥ delta * num_cpus →
      (hp_tasks.map (fun tsk_k => min (x_val tsk_k) delta)).sum ≥ delta * num_cpus := by
  sorry

theorem bertogna_fp_sum_exceeds_total_interference :
    let x_val := fun tsk_k => task_interference job_arrival job_cost job_task job_jitter sched j tsk_k
        (job_arrival j + job_jitter j) (job_arrival j + job_jitter j + R)
    (hp_bounds.map (fun ⟨tsk_k, _R_k⟩ =>
      min (x_val tsk_k) (R - task_cost tsk + 1))).sum >
    total_interference_bound_fp task_cost task_period task_jitter tsk hp_bounds R := by
  sorry

theorem bertogna_fp_exists_task_that_exceeds_bound :
    let x_val := fun tsk_k => task_interference job_arrival job_cost job_task job_jitter sched j tsk_k
        (job_arrival j + job_jitter j) (job_arrival j + job_jitter j + R)
    ∃ tsk_k R_k,
      (tsk_k, R_k) ∈ hp_bounds ∧
      min (x_val tsk_k) (R - task_cost tsk + 1) >
      min (W_jitter task_cost task_period task_jitter tsk_k R_k R)
          (R - task_cost tsk + 1) := by
  sorry

end DerivingContradiction

end Lemmas

include H_sporadic_tasks H_valid_job_parameters H_valid_task_parameters
  H_constrained_deadlines H_all_jobs_from_taskset H_jobs_come_from_arrival_sequence
  H_sequential_jobs H_jobs_execute_after_jitter H_completed_jobs_dont_execute
  H_at_least_one_cpu H_work_conserving H_respects_priority
  task_in_ts H_response_time_of_interfering_tasks_is_known
  H_hp_bounds_has_interfering_tasks H_response_time_bounds_ge_cost
  H_interfering_tasks_miss_no_deadlines H_response_time_recurrence_holds
  H_response_time_no_larger_than_deadline

theorem bertogna_cirinei_response_time_bound_fp :
    is_response_time_bound_of_task job_arrival job_cost job_task arr_seq sched tsk (task_jitter tsk + R) := by
  sorry

end ResponseTimeBound

end ResponseTimeAnalysisFP

end Prosa.Classic.Analysis.Global.Jitter.Bertogna_fp_theory
