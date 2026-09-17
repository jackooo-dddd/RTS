-- Translated from: ../rt-proofs/classic/analysis/apa/bertogna_fp_theory.v
import Prosa.Classic.Util.All
import Prosa.Classic.Model.Arrival.Basic.Task
import Prosa.Classic.Model.Arrival.Basic.Task_arrival
import Prosa.Classic.Model.Priority
import Prosa.Classic.Model.Schedule.Global.Workload
import Prosa.Classic.Model.Schedule.Global.Response_time
import Prosa.Classic.Model.Schedule.Global.Schedulability
import Prosa.Classic.Model.Schedule.Global.Basic.Schedule
import Prosa.Classic.Model.Schedule.Apa.Platform
import Prosa.Classic.Model.Schedule.Apa.Interference
import Prosa.Classic.Model.Schedule.Apa.Affinity
import Prosa.Classic.Model.Schedule.Apa.Constrained_deadlines
import Prosa.Classic.Analysis.Apa.Workload_bound
import Prosa.Classic.Analysis.Apa.Interference_bound
import Prosa.Classic.Analysis.Apa.Interference_bound_fp
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

set_option autoImplicit false

namespace Prosa.Classic.Analysis.Apa.Bertogna_fp_theory

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
open Prosa.Classic.Model.Schedule.Global.Workload
open Prosa.Classic.Model.Schedule.Apa.Platform
open Prosa.Classic.Model.Schedule.Apa.Interference
open Prosa.Classic.Model.Schedule.Apa.Affinity
open Prosa.Classic.Model.Schedule.Apa.Constrained_deadlines hiding apa_work_conserving respects_FP_policy_under_weak_APA
open Prosa.Classic.Model.Priority
open Prosa.Classic.Analysis.Apa.Workload_bound.WorkloadBound
open Prosa.Classic.Analysis.Apa.Interference_bound.InterferenceBoundGeneric
open Prosa.Classic.Analysis.Apa.Interference_bound_fp.InterferenceBoundFP
open Prosa.Util.Div_mod

attribute [local instance] Classical.propDecidable

namespace ResponseTimeAnalysisFP

section ResponseTimeBound

variable {sporadic_task : Type _} [DecidableEq sporadic_task]
variable (task_cost : sporadic_task → Time)
variable (task_period : sporadic_task → Time)
variable (task_deadline : sporadic_task → Time)

variable {Job : Type _} [DecidableEq Job]
variable (job_arrival : Job → Time)
variable (job_cost : Job → Time)
variable (job_deadline : Job → Time)
variable (job_task : Job → sporadic_task)

variable (arr_seq : arrival_sequence Job)

variable (H_sporadic_tasks :
  sporadic_task_model task_period job_arrival job_task arr_seq)

variable (H_valid_job_parameters :
  ∀ j, arrives_in arr_seq j →
    valid_sporadic_job task_cost task_deadline job_cost job_deadline job_task j)

variable (ts : List sporadic_task)

variable (H_valid_task_parameters :
  valid_sporadic_taskset task_cost task_period task_deadline ts)

variable (H_constrained_deadlines :
  ∀ tsk, tsk ∈ ts → task_deadline tsk ≤ task_period tsk)

variable (H_all_jobs_from_taskset :
  ∀ j, arrives_in arr_seq j → job_task j ∈ ts)

variable (H_ts_nodup : ts.Nodup)

variable {num_cpus : ℕ}
variable (alpha : task_affinity sporadic_task num_cpus)

variable (sched : schedule Job num_cpus)
variable (H_jobs_come_from_arrival_sequence :
  jobs_come_from_arrival_sequence sched arr_seq)

variable (H_sequential_jobs : sequential_jobs sched)
variable (H_jobs_must_arrive_to_execute :
  jobs_must_arrive_to_execute job_arrival sched)
variable (H_completed_jobs_dont_execute :
  completed_jobs_dont_execute job_cost sched)

variable (higher_eq_priority : FP_policy sporadic_task)

variable (H_respects_affinity : respects_affinity job_task sched alpha)
variable (H_work_conserving :
  apa_work_conserving job_arrival job_cost job_task arr_seq sched alpha)
variable (H_respects_FP_policy :
  respects_FP_policy_under_weak_APA job_arrival job_cost job_task arr_seq
    sched alpha higher_eq_priority)

variable (tsk : sporadic_task)
variable (task_in_ts : tsk ∈ ts)

variable (alpha' : task_affinity sporadic_task num_cpus)
variable (H_affinity_subset :
  ∀ tsk, tsk ∈ ts → is_subaffinity (alpha' tsk) (alpha tsk))
variable (H_at_least_one_cpu :
  ∀ tsk, tsk ∈ ts → (alpha' tsk).card > 0)

variable (hp_bounds : List (sporadic_task × Time))

variable (H_response_time_of_interfering_tasks_is_known :
  ∀ hp_tsk R,
    (hp_tsk, R) ∈ hp_bounds →
    is_response_time_bound_of_task job_arrival job_cost job_task arr_seq sched hp_tsk R)

variable (H_hp_bounds_has_interfering_tasks :
  ∀ hp_tsk,
    hp_tsk ∈ ts →
    higher_priority_task_in alpha higher_eq_priority tsk (alpha tsk) hp_tsk →
    ∃ R, (hp_tsk, R) ∈ hp_bounds)

variable (H_response_time_bounds_ge_cost :
  ∀ hp_tsk R, (hp_tsk, R) ∈ hp_bounds → R ≥ task_cost hp_tsk)

variable (H_interfering_tasks_miss_no_deadlines :
  ∀ hp_tsk R, (hp_tsk, R) ∈ hp_bounds → R ≤ task_deadline hp_tsk)

variable (R : Time)

variable (H_response_time_recurrence_holds :
  R = task_cost tsk +
    div_floor
      (total_interference_bound_fp task_cost task_period alpha tsk
        (alpha' tsk) hp_bounds R higher_eq_priority)
      (alpha' tsk).card)

variable (H_response_time_no_larger_than_deadline :
  R ≤ task_deadline tsk)

section Lemmas

variable (j : Job)
variable (H_j_arrives : arrives_in arr_seq j)
variable (H_job_of_tsk : job_task j = tsk)

variable (H_j_not_completed : ¬ completed job_cost sched j (job_arrival j + R))
variable (H_previous_jobs_of_tsk_completed :
  ∀ j0,
    arrives_in arr_seq j0 →
    job_task j0 = tsk →
    job_arrival j0 < job_arrival j →
    completed job_cost sched j0 (job_arrival j0 + R))

section LemmasAboutHPTasks

variable (tsk_other : sporadic_task)
variable (R_other : Time)
variable (H_tsk_other_already_processed : (tsk_other, R_other) ∈ hp_bounds)
variable (H_tsk_other_has_higher_priority :
  higher_priority_task_in alpha higher_eq_priority tsk (alpha tsk) tsk_other)

include H_sporadic_tasks H_valid_job_parameters H_valid_task_parameters
  H_constrained_deadlines H_all_jobs_from_taskset H_jobs_come_from_arrival_sequence
  H_sequential_jobs H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
  H_respects_affinity H_work_conserving H_respects_FP_policy
  task_in_ts H_affinity_subset H_at_least_one_cpu
  H_response_time_of_interfering_tasks_is_known H_hp_bounds_has_interfering_tasks
  H_response_time_bounds_ge_cost H_interfering_tasks_miss_no_deadlines
  H_response_time_recurrence_holds H_response_time_no_larger_than_deadline
  H_j_arrives H_job_of_tsk H_j_not_completed H_previous_jobs_of_tsk_completed
  H_tsk_other_already_processed

include H_sporadic_tasks H_valid_job_parameters H_valid_task_parameters H_constrained_deadlines H_all_jobs_from_taskset H_jobs_come_from_arrival_sequence H_sequential_jobs H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_respects_affinity H_work_conserving H_respects_FP_policy H_affinity_subset H_at_least_one_cpu H_response_time_of_interfering_tasks_is_known H_hp_bounds_has_interfering_tasks H_response_time_bounds_ge_cost H_interfering_tasks_miss_no_deadlines H_response_time_recurrence_holds H_response_time_no_larger_than_deadline H_j_arrives H_job_of_tsk H_j_not_completed H_previous_jobs_of_tsk_completed H_tsk_other_already_processed in
theorem bertogna_fp_workload_bounds_interference :
    task_interference job_arrival job_cost job_task sched alpha j tsk_other
      (job_arrival j) (job_arrival j + R) ≤
    W task_cost task_period tsk_other R_other R := by
  -- Step 1: bound task_interference by workload
  have hStep1 :
      task_interference job_arrival job_cost job_task sched alpha j tsk_other
        (job_arrival j) (job_arrival j + R) ≤
      workload job_task sched tsk_other (job_arrival j) (job_arrival j + R) :=
    task_interference_le_workload job_arrival job_cost job_task sched alpha j
      tsk_other (job_arrival j) (job_arrival j + R)
  -- Step 2: bound workload by W
  by_cases hTOin : tsk_other ∈ ts
  · have hValidOther : is_valid_sporadic_task task_cost task_period task_deadline tsk_other :=
      H_valid_task_parameters tsk_other hTOin
    have hConstrOther : task_deadline tsk_other ≤ task_period tsk_other :=
      H_constrained_deadlines tsk_other hTOin
    have hRgeCost : R_other ≥ task_cost tsk_other :=
      H_response_time_bounds_ge_cost tsk_other R_other H_tsk_other_already_processed
    have hRleD : R_other ≤ task_deadline tsk_other :=
      H_interfering_tasks_miss_no_deadlines tsk_other R_other H_tsk_other_already_processed
    have hRespBound : ∀ (j' : Job),
        arrives_in arr_seq j' → job_task j' = tsk_other →
        job_arrival j' + R_other < job_arrival j + R →
        completed job_cost sched j' (job_arrival j' + R_other) := by
      intro j' hARR' hJOB' _
      exact H_response_time_of_interfering_tasks_is_known tsk_other R_other
        H_tsk_other_already_processed j' hARR' hJOB'
    have hWB :=
      Prosa.Classic.Analysis.Apa.Workload_bound.WorkloadBound.workload_bounded_by_W
        task_cost task_period task_deadline job_arrival job_cost job_task job_deadline
        arr_seq H_valid_job_parameters
        (num_cpus := num_cpus) sched H_jobs_come_from_arrival_sequence
        H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_sequential_jobs
        H_sporadic_tasks tsk_other hValidOther hConstrOther
        (job_arrival j) R R_other hRespBound hRgeCost hRleD
    exact le_trans hStep1 hWB
  · have hWZero : workload job_task sched tsk_other (job_arrival j) (job_arrival j + R) = 0 := by
      unfold workload
      apply Finset.sum_eq_zero
      intro t _
      apply Finset.sum_eq_zero
      intro cpu _
      unfold service_of_task
      cases h_sc : sched cpu t with
      | none => rfl
      | some j' =>
        have hARR' : arrives_in arr_seq j' :=
          H_jobs_come_from_arrival_sequence j' t ⟨cpu, by unfold scheduled_on; rw [h_sc]; simp⟩
        have hInTs : job_task j' ∈ ts := H_all_jobs_from_taskset j' hARR'
        have hNeq : job_task j' ≠ tsk_other := by
          intro h; rw [h] at hInTs; exact hTOin hInTs
        simp [hNeq]
    have hWZ_le : workload job_task sched tsk_other (job_arrival j) (job_arrival j + R) ≤
        W task_cost task_period tsk_other R_other R := by
      rw [hWZero]; exact Nat.zero_le _
    exact le_trans hStep1 hWZ_le

end LemmasAboutHPTasks

section DerivingContradiction

include H_sporadic_tasks H_valid_job_parameters H_valid_task_parameters
  H_constrained_deadlines H_all_jobs_from_taskset H_jobs_come_from_arrival_sequence
  H_sequential_jobs H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
  H_respects_affinity H_work_conserving H_respects_FP_policy
  task_in_ts H_affinity_subset H_at_least_one_cpu
  H_response_time_of_interfering_tasks_is_known H_hp_bounds_has_interfering_tasks
  H_response_time_bounds_ge_cost H_interfering_tasks_miss_no_deadlines
  H_response_time_recurrence_holds H_response_time_no_larger_than_deadline
  H_j_arrives H_job_of_tsk H_j_not_completed H_previous_jobs_of_tsk_completed

include H_sporadic_tasks H_valid_job_parameters H_valid_task_parameters H_constrained_deadlines H_all_jobs_from_taskset H_jobs_come_from_arrival_sequence H_sequential_jobs H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_respects_affinity H_work_conserving H_respects_FP_policy H_affinity_subset H_at_least_one_cpu H_response_time_of_interfering_tasks_is_known H_hp_bounds_has_interfering_tasks H_response_time_bounds_ge_cost H_interfering_tasks_miss_no_deadlines H_response_time_recurrence_holds H_response_time_no_larger_than_deadline H_j_arrives H_job_of_tsk H_j_not_completed H_previous_jobs_of_tsk_completed in
theorem bertogna_fp_too_much_interference :
    total_interference job_arrival job_cost sched j
      (job_arrival j) (job_arrival j + R) ≥
    R - task_cost tsk + 1 := by
  set X := total_interference job_arrival job_cost sched j
              (job_arrival j) (job_arrival j + R) with hXdef
  have hCostLe : job_cost j ≤ task_cost tsk := by
    have hVJP := H_valid_job_parameters j H_j_arrives
    have hcost := hVJP.2.1
    unfold job_cost_le_task_cost at hcost
    rw [H_job_of_tsk] at hcost
    exact hcost
  have hServLt : service sched j (job_arrival j + R) < job_cost j := by
    by_contra hge
    push_neg at hge
    exact H_j_not_completed hge
  have hSlot : ∀ t ∈ Finset.Ico (job_arrival j) (job_arrival j + R),
      (1 : ℕ) ≤ (if backlogged job_arrival job_cost sched j t then 1 else 0) +
                  service_at sched j t := by
    intro t ht
    rw [Finset.mem_Ico] at ht
    by_cases hback : backlogged job_arrival job_cost sched j t
    · simp [hback]
    · simp only [hback, if_false, zero_add]
      unfold backlogged at hback
      push_neg at hback
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
      · have hNotPending : ¬ pending job_arrival job_cost sched j t := by
          intro hP
          exact hSched (hback hP)
        unfold pending at hNotPending
        push_neg at hNotPending
        have hArr : has_arrived job_arrival j t := ht.1
        have hCompT : completed job_cost sched j t := hNotPending hArr
        have hCompR : completed job_cost sched j (job_arrival j + R) :=
          completion_monotonic job_cost sched j H_completed_jobs_dont_execute
            t (job_arrival j + R) (le_of_lt ht.2) hCompT
        exact absurd hCompR H_j_not_completed
  have hCardR : (Finset.Ico (job_arrival j) (job_arrival j + R)).card = R := by
    rw [Nat.card_Ico]; omega
  have hSum :
      R ≤ X + ∑ t ∈ Finset.Ico (job_arrival j) (job_arrival j + R), service_at sched j t := by
    have h1 :
        ∑ _t ∈ Finset.Ico (job_arrival j) (job_arrival j + R), (1 : ℕ) ≤
        ∑ t ∈ Finset.Ico (job_arrival j) (job_arrival j + R),
          ((if backlogged job_arrival job_cost sched j t then 1 else 0) +
           service_at sched j t) := Finset.sum_le_sum hSlot
    rw [Finset.sum_const, Nat.smul_one_eq_cast, hCardR] at h1
    simp only [Nat.cast_id] at h1
    rw [Finset.sum_add_distrib] at h1
    have hXunfold :
        ∑ t ∈ Finset.Ico (job_arrival j) (job_arrival j + R),
          (if backlogged job_arrival job_cost sched j t then 1 else 0) = X := by
      rw [hXdef]; rfl
    rw [hXunfold] at h1
    exact h1
  have hServEq :
      ∑ t ∈ Finset.Ico (job_arrival j) (job_arrival j + R), service_at sched j t =
      service sched j (job_arrival j + R) := by
    unfold service
    have := service_before_arrival_eq_service_during
              job_arrival sched j H_jobs_must_arrive_to_execute
              0 R (Nat.zero_le _)
    exact this.symm
  rw [hServEq] at hSum
  have hCostLeR : task_cost tsk ≤ R := by
    rw [H_response_time_recurrence_holds]; exact Nat.le_add_right _ _
  have hCancel : (R - task_cost tsk) + task_cost tsk = R :=
    Nat.sub_add_cancel hCostLeR
  have hStep : R + 1 ≤ X + task_cost tsk :=
    calc R + 1
        ≤ (X + service sched j (job_arrival j + R)) + 1 :=
          Nat.add_le_add_right hSum 1
      _ = X + (service sched j (job_arrival j + R) + 1) := (Nat.add_assoc _ _ _)
      _ ≤ X + job_cost j := Nat.add_le_add_left hServLt X
      _ ≤ X + task_cost tsk := Nat.add_le_add_left hCostLe X
  have hStep' : (R - task_cost tsk + 1) + task_cost tsk ≤ X + task_cost tsk := by
    have : (R - task_cost tsk + 1) + task_cost tsk = R + 1 := by
      rw [Nat.add_right_comm]; rw [hCancel]
    rw [this]; exact hStep
  exact Nat.le_of_add_le_add_right hStep'

theorem bertogna_fp_interference_by_different_tasks :
    ∀ t j_other,
      job_arrival j ≤ t ∧ t < job_arrival j + R →
      arrives_in arr_seq j_other →
      backlogged job_arrival job_cost sched j t →
      scheduled sched j_other t →
      job_task j_other ≠ tsk := by
  intro t j_other ⟨LEt, GEt⟩ ARRother BACK SCHED SAMEtsk
  -- j_other is scheduled so it's pending
  have PENDING := scheduled_implies_pending job_arrival job_cost sched j_other
    H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute t SCHED
  obtain ⟨ARRIVED_other, NOTCOMP_other⟩ := PENDING
  by_cases BEFOREother : job_arrival j_other < job_arrival j
  · -- Case 1: j_other arrived before j
    have BEFOREok := H_previous_jobs_of_tsk_completed j_other ARRother SAMEtsk BEFOREother
    -- j_other should be completed by job_arrival j_other + R
    -- We need: job_arrival j_other + R ≤ t
    -- From BEFOREok: completed at job_arrival j_other + R
    -- completed at j_other + R, and t ≥ job_arrival j, and j_other + R < j + R (since j_other < j)
    -- Actually: we need R ≤ task_deadline tsk ≤ task_period tsk
    -- And job_arrival j ≤ job_arrival j_other + task_period tsk (sporadic model)
    -- So job_arrival j_other + R ≤ job_arrival j_other + task_deadline tsk ≤ job_arrival j_other + task_period tsk ≤ job_arrival j ≤ t
    have h1 : job_arrival j_other + R ≤ job_arrival j_other + task_deadline tsk := by
      apply Nat.add_le_add_left H_response_time_no_larger_than_deadline
    have h2 : job_arrival j_other + task_deadline tsk ≤ job_arrival j_other + task_period tsk := by
      apply Nat.add_le_add_left
      exact H_constrained_deadlines tsk task_in_ts
    have FROMTS_other := H_all_jobs_from_taskset j_other ARRother
    have h3 : job_arrival j_other + task_period tsk ≤ job_arrival j := by
      -- From sporadic model: j ≠ j_other, same task, j_other arrives first
      have hne : j_other ≠ j := by
        intro heq; subst heq; exact Nat.lt_irrefl _ BEFOREother
      have same_task' : job_task j_other = job_task j := by rw [SAMEtsk, H_job_of_tsk]
      have SPO' := H_sporadic_tasks j_other j hne ARRother H_j_arrives same_task' (le_of_lt BEFOREother)
      rw [same_task', H_job_of_tsk] at SPO'
      exact SPO'
    have h4 : job_arrival j_other + R ≤ t := le_trans (le_trans (le_trans h1 h2) h3) LEt
    have COMP := completion_monotonic job_cost sched j_other H_completed_jobs_dont_execute
      (job_arrival j_other + R) t h4 BEFOREok
    exact NOTCOMP_other COMP
  · -- Case 2: j_other arrived at or after j
    push_neg at BEFOREother
    -- j and j_other are of the same task, j arrived no later than j_other
    -- If j = j_other, then j is both backlogged and scheduled, contradiction
    -- If j ≠ j_other, by sporadic model, j_other arrives ≥ job_arrival j + task_period tsk
    --   But j_other is pending at t < job_arrival j + R ≤ job_arrival j + task_deadline tsk ≤ job_arrival j + task_period tsk
    --   So job_arrival j_other ≤ t < job_arrival j + task_period tsk
    --   Contradiction with j_other arriving ≥ job_arrival j + task_period tsk
    by_cases heq : j_other = j
    · -- j_other = j, but j is backlogged (not scheduled) and j_other is scheduled: contradiction
      subst heq
      obtain ⟨_, hnotsched⟩ := BACK
      exact hnotsched SCHED
    · -- j ≠ j_other, both of task tsk
      have same_task : job_task j = job_task j_other := by rw [H_job_of_tsk, SAMEtsk]
      have SPO := H_sporadic_tasks j j_other (Ne.symm heq) H_j_arrives ARRother
        same_task BEFOREother
      -- SPO : job_arrival j_other ≥ job_arrival j + task_period (job_task j)
      -- ARRIVED_other : job_arrival j_other ≤ t (has_arrived)
      -- GEt : t < job_arrival j + R
      -- So job_arrival j + task_period (job_task j) ≤ job_arrival j_other ≤ t < job_arrival j + R
      -- ≤ job_arrival j + task_deadline tsk ≤ job_arrival j + task_period tsk
      -- = job_arrival j + task_period (job_task j) (by H_job_of_tsk)
      -- This gives task_period (job_task j) ≤ ... < task_period (job_task j), contradiction
      -- SPO: job_arrival j_other ≥ job_arrival j + task_period (job_task j)
      -- ARRIVED_other: has_arrived ≡ job_arrival j_other ≤ t
      -- GEt: t < job_arrival j + R
      -- These together with R ≤ deadline ≤ period give contradiction
      have harr : job_arrival j_other ≤ t := ARRIVED_other
      have h1 : job_arrival j + task_period (job_task j) ≤ t := le_trans SPO harr
      rw [H_job_of_tsk] at h1
      have h3 : R ≤ task_deadline tsk := H_response_time_no_larger_than_deadline
      have h4 : task_deadline tsk ≤ task_period tsk := H_constrained_deadlines tsk task_in_ts
      -- h1: job_arrival j + task_period tsk ≤ t
      -- GEt: t < job_arrival j + R
      -- So task_period tsk < R ≤ task_deadline tsk ≤ task_period tsk, contradiction
      have h5 : t < job_arrival j + task_period tsk :=
        lt_of_lt_of_le GEt (Nat.add_le_add_left (le_trans h3 h4) _)
      exact absurd h1 (not_le.mpr h5)

theorem bertogna_fp_previous_interfering_jobs_complete_by_their_period :
    ∀ j0,
      arrives_in arr_seq j0 →
      higher_priority_task_in alpha higher_eq_priority tsk (alpha tsk) (job_task j0) →
      completed job_cost sched j0
        (job_arrival j0 + task_period (job_task j0)) := by
  intro j0 ARR0 INTERF
  have FROMTS := H_all_jobs_from_taskset j0 ARR0
  obtain ⟨R0, INbounds0⟩ := H_hp_bounds_has_interfering_tasks (job_task j0) FROMTS INTERF
  apply completion_monotonic job_cost sched j0 H_completed_jobs_dont_execute
    (job_arrival j0 + R0) (job_arrival j0 + task_period (job_task j0))
  · apply Nat.add_le_add_left
    apply le_trans (H_interfering_tasks_miss_no_deadlines (job_task j0) R0 INbounds0)
    exact H_constrained_deadlines (job_task j0) FROMTS
  · exact H_response_time_of_interfering_tasks_is_known (job_task j0) R0 INbounds0 j0 ARR0 rfl

include H_sporadic_tasks H_valid_job_parameters H_valid_task_parameters H_constrained_deadlines H_all_jobs_from_taskset H_jobs_come_from_arrival_sequence H_sequential_jobs H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_respects_affinity H_work_conserving H_respects_FP_policy H_affinity_subset H_at_least_one_cpu H_response_time_of_interfering_tasks_is_known H_hp_bounds_has_interfering_tasks H_response_time_bounds_ge_cost H_interfering_tasks_miss_no_deadlines H_response_time_recurrence_holds H_response_time_no_larger_than_deadline H_j_arrives H_job_of_tsk H_j_not_completed H_previous_jobs_of_tsk_completed H_ts_nodup in
set_option maxHeartbeats 800000 in
theorem bertogna_fp_all_cpus_in_affinity_busy :
    ((ts.filter (fun tsk_other =>
      decide (higher_priority_task_in alpha higher_eq_priority tsk (alpha tsk) tsk_other))).map
      (fun tsk_k => task_interference job_arrival job_cost job_task sched alpha j tsk_k
        (job_arrival j) (job_arrival j + R))).sum =
    total_interference job_arrival job_cost sched j
      (job_arrival j) (job_arrival j + R) * (alpha tsk).card := by
  set hp_tasks := ts.filter (fun tsk_other =>
    decide (higher_priority_task_in alpha higher_eq_priority tsk (alpha tsk) tsk_other))
    with hp_def
  have hSwap1 : ∀ (L : List sporadic_task) (S : Finset ℕ) (f : sporadic_task → ℕ → ℕ),
      (L.map (fun x => ∑ i ∈ S, f x i)).sum = ∑ i ∈ S, (L.map (fun x => f x i)).sum := by
    intro L S f; induction L with | nil => simp | cons a t ih => simp [ih, Finset.sum_add_distrib]
  have hSwap2 : ∀ (L : List sporadic_task) (f : sporadic_task → Fin num_cpus → ℕ),
      (L.map (fun x => ∑ i : Fin num_cpus, f x i)).sum =
        ∑ i : Fin num_cpus, (L.map (fun x => f x i)).sum := by
    intro L f; induction L with | nil => simp | cons a t ih => simp [ih, Finset.sum_add_distrib]
  show (((hp_tasks.map (fun tsk_k =>
      ∑ t ∈ Finset.Ico (job_arrival j) (job_arrival j + R),
        ∑ cpu : Fin num_cpus,
          if backlogged job_arrival job_cost sched j t ∧
             can_execute_on alpha (job_task j) cpu ∧
             task_scheduled_on job_task sched tsk_k cpu t = true then 1 else 0)).sum) =
    ((∑ t ∈ Finset.Ico (job_arrival j) (job_arrival j + R),
      if backlogged job_arrival job_cost sched j t then 1 else 0) * (alpha tsk).card))
  rw [hSwap1 hp_tasks (Finset.Ico (job_arrival j) (job_arrival j + R))
        (fun tsk_k t => ∑ cpu : Fin num_cpus,
          if backlogged job_arrival job_cost sched j t ∧
             can_execute_on alpha (job_task j) cpu ∧
             task_scheduled_on job_task sched tsk_k cpu t = true then 1 else 0)]
  simp_rw [hSwap2 hp_tasks]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro t ht
  rw [Finset.mem_Ico] at ht
  by_cases hBack : backlogged job_arrival job_cost sched j t
  · rw [if_pos hBack, one_mul]
    have hPerCpu : ∀ cpu : Fin num_cpus,
        (hp_tasks.map (fun tsk_k => if backlogged job_arrival job_cost sched j t ∧
            can_execute_on alpha (job_task j) cpu ∧
            task_scheduled_on job_task sched tsk_k cpu t = true then (1:ℕ) else 0)).sum =
        if cpu ∈ alpha tsk then 1 else 0 := by
      intro cpu
      by_cases hAlpha : cpu ∈ alpha tsk
      · rw [if_pos hAlpha]
        have hCE : can_execute_on alpha (job_task j) cpu := by
          unfold can_execute_on; rw [H_job_of_tsk]; exact hAlpha
        obtain ⟨j_other, hOn⟩ := H_work_conserving j t H_j_arrives hBack cpu hCE
        have hSchedOther : scheduled sched j_other t := ⟨cpu, hOn⟩
        have hARRother : arrives_in arr_seq j_other :=
          H_jobs_come_from_arrival_sequence j_other t hSchedOther
        have hFP : higher_eq_priority (job_task j_other) (job_task j) = true :=
          H_respects_FP_policy j j_other cpu t H_j_arrives hBack hOn hCE
        have hDIFF : job_task j_other ≠ tsk :=
          bertogna_fp_interference_by_different_tasks task_cost task_period task_deadline
            job_arrival job_cost job_deadline job_task arr_seq H_sporadic_tasks
            H_valid_job_parameters ts H_valid_task_parameters
            H_constrained_deadlines H_all_jobs_from_taskset
            (num_cpus := num_cpus) alpha sched H_jobs_come_from_arrival_sequence
            H_sequential_jobs H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
            higher_eq_priority H_respects_affinity H_work_conserving H_respects_FP_policy
            tsk task_in_ts alpha' H_affinity_subset H_at_least_one_cpu hp_bounds
            H_response_time_of_interfering_tasks_is_known H_hp_bounds_has_interfering_tasks
            H_response_time_bounds_ge_cost H_interfering_tasks_miss_no_deadlines R
            H_response_time_recurrence_holds H_response_time_no_larger_than_deadline
            j H_j_arrives H_job_of_tsk H_j_not_completed H_previous_jobs_of_tsk_completed
            t j_other ⟨ht.1, ht.2⟩ hARRother hBack hSchedOther
        have hAPA : can_execute_on alpha (job_task j_other) cpu :=
          H_respects_affinity j_other cpu t hOn
        have hOtherInTs : job_task j_other ∈ ts :=
          H_all_jobs_from_taskset j_other hARRother
        have hOtherInHp : job_task j_other ∈ hp_tasks := by
          rw [hp_def, List.mem_filter]
          exact ⟨hOtherInTs, decide_eq_true_eq.mpr
            ⟨by rw [H_job_of_tsk] at hFP; exact hFP, hDIFF, ⟨cpu, hAlpha, hAPA⟩⟩⟩
        have hTSOn : task_scheduled_on job_task sched (job_task j_other) cpu t = true := by
          unfold task_scheduled_on; unfold scheduled_on at hOn
          cases h_sc : sched cpu t with
          | none => rw [h_sc] at hOn; simp at hOn
          | some j' => rw [h_sc] at hOn; simp at hOn; subst hOn; simp
        have hOtherZero : ∀ tsk_k, tsk_k ≠ job_task j_other →
            (if backlogged job_arrival job_cost sched j t ∧
                can_execute_on alpha (job_task j) cpu ∧
                task_scheduled_on job_task sched tsk_k cpu t = true then (1:ℕ) else 0) = 0 := by
          intro tsk_k hNeq
          have hTaskFalse : task_scheduled_on job_task sched tsk_k cpu t = false := by
            unfold task_scheduled_on; unfold scheduled_on at hOn
            cases h_sc : sched cpu t with
            | none => rfl
            | some j' =>
              simp only; have hjj : j' = j_other := by rw [h_sc] at hOn; simp at hOn; exact hOn
              subst hjj; simp [hNeq.symm]
          simp [hTaskFalse]
        have hHpNodup : hp_tasks.Nodup := List.Nodup.filter _ H_ts_nodup
        rw [← List.sum_toFinset _ hHpNodup]
        rw [Finset.sum_eq_single (job_task j_other)]
        · simp [hBack, hCE, hTSOn]
        · intro tsk_k _ hNeq; exact hOtherZero tsk_k hNeq
        · intro hNotMem; exfalso; exact hNotMem (List.mem_toFinset.mpr hOtherInHp)
      · rw [if_neg hAlpha]
        apply List.sum_eq_zero
        intro x hx; obtain ⟨tsk_k, _, h_eq⟩ := List.mem_map.mp hx
        rw [← h_eq, if_neg]; intro ⟨_, hCE, _⟩
        exact hAlpha (by unfold can_execute_on at hCE; rw [H_job_of_tsk] at hCE; exact hCE)
    simp_rw [hPerCpu]
    rw [← Finset.sum_filter (s := Finset.univ)]
    have : Finset.univ.filter (fun x : Fin num_cpus => x ∈ alpha tsk) = alpha tsk := by
      ext x; simp
    rw [this, Finset.card_eq_sum_ones]
  · rw [if_neg hBack, zero_mul]
    apply Finset.sum_eq_zero; intro cpu _
    apply List.sum_eq_zero; intro x hx
    obtain ⟨tsk_k, _, h_eq⟩ := List.mem_map.mp hx
    rw [← h_eq, if_neg]; intro ⟨h1, _⟩; exact hBack h1

include H_sporadic_tasks H_valid_job_parameters H_valid_task_parameters H_constrained_deadlines H_all_jobs_from_taskset H_jobs_come_from_arrival_sequence H_sequential_jobs H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_respects_affinity H_work_conserving H_respects_FP_policy H_affinity_subset H_at_least_one_cpu H_response_time_of_interfering_tasks_is_known H_hp_bounds_has_interfering_tasks H_response_time_bounds_ge_cost H_interfering_tasks_miss_no_deadlines H_response_time_recurrence_holds H_response_time_no_larger_than_deadline H_j_arrives H_job_of_tsk H_j_not_completed H_previous_jobs_of_tsk_completed in
set_option maxHeartbeats 800000 in
theorem bertogna_fp_all_cpus_in_subaffinity_busy :
    ((ts.filter (fun tsk_other =>
      decide (higher_priority_task_in alpha higher_eq_priority tsk (alpha' tsk) tsk_other))).map
      (fun tsk_k => task_interference job_arrival job_cost job_task sched alpha j tsk_k
        (job_arrival j) (job_arrival j + R))).sum ≥
    total_interference job_arrival job_cost sched j
      (job_arrival j) (job_arrival j + R) * (alpha' tsk).card := by
  set hp_tasks := ts.filter (fun tsk_other =>
    decide (higher_priority_task_in alpha higher_eq_priority tsk (alpha' tsk) tsk_other))
    with hp_def
  have hSwap1 : ∀ (L : List sporadic_task) (S : Finset ℕ) (f : sporadic_task → ℕ → ℕ),
      (L.map (fun x => ∑ i ∈ S, f x i)).sum = ∑ i ∈ S, (L.map (fun x => f x i)).sum := by
    intro L S f; induction L with | nil => simp | cons a t ih => simp [ih, Finset.sum_add_distrib]
  have hSwap2 : ∀ (L : List sporadic_task) (f : sporadic_task → Fin num_cpus → ℕ),
      (L.map (fun x => ∑ i : Fin num_cpus, f x i)).sum =
        ∑ i : Fin num_cpus, (L.map (fun x => f x i)).sum := by
    intro L f; induction L with | nil => simp | cons a t ih => simp [ih, Finset.sum_add_distrib]
  show (((hp_tasks.map (fun tsk_k =>
      ∑ t ∈ Finset.Ico (job_arrival j) (job_arrival j + R),
        ∑ cpu : Fin num_cpus,
          if backlogged job_arrival job_cost sched j t ∧
             can_execute_on alpha (job_task j) cpu ∧
             task_scheduled_on job_task sched tsk_k cpu t = true then 1 else 0)).sum) ≥
    ((∑ t ∈ Finset.Ico (job_arrival j) (job_arrival j + R),
      if backlogged job_arrival job_cost sched j t then 1 else 0) * (alpha' tsk).card))
  rw [hSwap1 hp_tasks (Finset.Ico (job_arrival j) (job_arrival j + R))
        (fun tsk_k t => ∑ cpu : Fin num_cpus,
          if backlogged job_arrival job_cost sched j t ∧
             can_execute_on alpha (job_task j) cpu ∧
             task_scheduled_on job_task sched tsk_k cpu t = true then 1 else 0)]
  simp_rw [hSwap2 hp_tasks]
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro t ht
  rw [Finset.mem_Ico] at ht
  by_cases hBack : backlogged job_arrival job_cost sched j t
  · rw [if_pos hBack, one_mul]
    have hSub := H_affinity_subset (job_task j) (H_all_jobs_from_taskset j H_j_arrives)
    calc (alpha' tsk).card
        = ∑ _cpu ∈ (alpha' tsk), (1 : ℕ) := by rw [Finset.card_eq_sum_ones]
      _ ≤ ∑ cpu ∈ (alpha' tsk),
            (hp_tasks.map (fun tsk_k => if backlogged job_arrival job_cost sched j t ∧
                can_execute_on alpha (job_task j) cpu ∧
                task_scheduled_on job_task sched tsk_k cpu t = true then (1:ℕ) else 0)).sum := by
          apply Finset.sum_le_sum; intro cpu hcpu
          have hAlpha : cpu ∈ alpha tsk := by rw [H_job_of_tsk] at hSub; exact hSub cpu hcpu
          have hCE : can_execute_on alpha (job_task j) cpu := by
            unfold can_execute_on; rw [H_job_of_tsk]; exact hAlpha
          obtain ⟨j_other, hOn⟩ := H_work_conserving j t H_j_arrives hBack cpu hCE
          have hSchedOther : scheduled sched j_other t := ⟨cpu, hOn⟩
          have hARRother := H_jobs_come_from_arrival_sequence j_other t hSchedOther
          have hFP := H_respects_FP_policy j j_other cpu t H_j_arrives hBack hOn hCE
          have hDIFF :=
            bertogna_fp_interference_by_different_tasks task_cost task_period task_deadline
              job_arrival job_cost job_deadline job_task arr_seq H_sporadic_tasks
              H_valid_job_parameters ts H_valid_task_parameters
              H_constrained_deadlines H_all_jobs_from_taskset
              (num_cpus := num_cpus) alpha sched H_jobs_come_from_arrival_sequence
              H_sequential_jobs H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
              higher_eq_priority H_respects_affinity H_work_conserving H_respects_FP_policy
              tsk task_in_ts alpha' H_affinity_subset H_at_least_one_cpu hp_bounds
              H_response_time_of_interfering_tasks_is_known H_hp_bounds_has_interfering_tasks
              H_response_time_bounds_ge_cost H_interfering_tasks_miss_no_deadlines R
              H_response_time_recurrence_holds H_response_time_no_larger_than_deadline
              j H_j_arrives H_job_of_tsk H_j_not_completed H_previous_jobs_of_tsk_completed
              t j_other ⟨ht.1, ht.2⟩ hARRother hBack hSchedOther
          have hAPA := H_respects_affinity j_other cpu t hOn
          have hOtherInHp : job_task j_other ∈ hp_tasks := by
            rw [hp_def, List.mem_filter]
            exact ⟨H_all_jobs_from_taskset j_other hARRother, decide_eq_true_eq.mpr
              ⟨by rw [H_job_of_tsk] at hFP; exact hFP, hDIFF, ⟨cpu, hcpu, hAPA⟩⟩⟩
          have hVal : (if backlogged job_arrival job_cost sched j t ∧
              can_execute_on alpha (job_task j) cpu ∧
              task_scheduled_on job_task sched (job_task j_other) cpu t = true then (1:ℕ) else 0) = 1 := by
            rw [if_pos]; refine ⟨hBack, hCE, ?_⟩
            unfold task_scheduled_on; unfold scheduled_on at hOn
            cases h_sc : sched cpu t with
            | none => rw [h_sc] at hOn; simp at hOn
            | some j' => rw [h_sc] at hOn; simp at hOn; subst hOn; simp
          calc (1:ℕ)
              = (if backlogged job_arrival job_cost sched j t ∧
                  can_execute_on alpha (job_task j) cpu ∧
                  task_scheduled_on job_task sched (job_task j_other) cpu t = true
                then (1:ℕ) else 0) := hVal.symm
            _ ≤ (hp_tasks.map (fun tsk_k => if backlogged job_arrival job_cost sched j t ∧
                    can_execute_on alpha (job_task j) cpu ∧
                    task_scheduled_on job_task sched tsk_k cpu t = true then (1:ℕ) else 0)).sum :=
                List.single_le_sum (fun x _ => Nat.zero_le x)
                  _ (List.mem_map.mpr ⟨job_task j_other, hOtherInHp, rfl⟩)
      _ ≤ ∑ cpu : Fin num_cpus,
            (hp_tasks.map (fun tsk_k => if backlogged job_arrival job_cost sched j t ∧
                can_execute_on alpha (job_task j) cpu ∧
                task_scheduled_on job_task sched tsk_k cpu t = true then (1:ℕ) else 0)).sum :=
          Finset.sum_le_sum_of_subset_of_nonneg (fun x hx => Finset.mem_univ x)
            (fun _ _ _ => Nat.zero_le _)
  · rw [if_neg hBack, zero_mul]
    apply Nat.zero_le

include H_sporadic_tasks H_valid_job_parameters H_valid_task_parameters H_constrained_deadlines H_all_jobs_from_taskset H_jobs_come_from_arrival_sequence H_sequential_jobs H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_respects_affinity H_work_conserving H_respects_FP_policy H_affinity_subset H_at_least_one_cpu H_response_time_of_interfering_tasks_is_known H_hp_bounds_has_interfering_tasks H_response_time_bounds_ge_cost H_interfering_tasks_miss_no_deadlines H_response_time_recurrence_holds H_response_time_no_larger_than_deadline H_j_arrives H_job_of_tsk H_j_not_completed H_previous_jobs_of_tsk_completed H_ts_nodup in
set_option maxHeartbeats 800000 in
theorem bertogna_fp_alpha'_is_full :
    ∀ t,
      job_arrival j ≤ t ∧ t < job_arrival j + R →
      backlogged job_arrival job_cost sched j t →
      (ts.filter (fun tsk_other =>
        decide (higher_priority_task_in alpha higher_eq_priority tsk (alpha' tsk) tsk_other))).countP
        (fun tsk_k => decide (task_scheduled_on_affinity job_task sched (alpha tsk) tsk_k t)) ≥
      (alpha' tsk).card := by
  intro t ht hBack
  set hp := ts.filter (fun tsk_other =>
    decide (higher_priority_task_in alpha higher_eq_priority tsk (alpha' tsk) tsk_other))
    with hp_def
  set p := fun tsk_k => decide (task_scheduled_on_affinity job_task sched (alpha tsk) tsk_k t)
  have hSub' : ∀ cpu, cpu ∈ alpha' tsk → cpu ∈ alpha tsk :=
    H_affinity_subset tsk task_in_ts
  -- HP jobs complete by their period
  have hPrevHP : ∀ (j0 : Job),
      arrives_in arr_seq j0 →
      higher_priority_task_in alpha higher_eq_priority tsk (alpha tsk) (job_task j0) →
      completed job_cost sched j0 (job_arrival j0 + task_period (job_task j0)) := by
    intro j0 hA0 hHP0
    have hIn0 := H_all_jobs_from_taskset j0 hA0
    obtain ⟨R0, hR0⟩ := H_hp_bounds_has_interfering_tasks (job_task j0) hIn0 hHP0
    exact completion_monotonic job_cost sched j0 H_completed_jobs_dont_execute _ _ (by
      apply Nat.add_le_add_left
      exact le_trans (H_interfering_tasks_miss_no_deadlines _ R0 hR0)
        (H_constrained_deadlines _ hIn0))
      (H_response_time_of_interfering_tasks_is_known _ R0 hR0 j0 hA0 rfl)
  -- For each cpu in alpha'(tsk), extract the scheduled job
  have hAssign : ∀ cpu ∈ alpha' tsk, ∃ j_cpu,
      sched cpu t = some j_cpu ∧
      job_task j_cpu ∈ hp ∧ p (job_task j_cpu) = true := by
    intro cpu hcpu
    have hAlpha := hSub' cpu hcpu
    have hCE : can_execute_on alpha (job_task j) cpu := by
      unfold can_execute_on; rw [H_job_of_tsk]; exact hAlpha
    obtain ⟨j_other, hOn⟩ := H_work_conserving j t H_j_arrives hBack cpu hCE
    have hSch : sched cpu t = some j_other := by
      unfold scheduled_on at hOn
      cases h_sc : sched cpu t with
      | none => rw [h_sc] at hOn; simp at hOn
      | some j' => rw [h_sc] at hOn; simp at hOn; subst hOn; rfl
    have hSchedOther : scheduled sched j_other t := ⟨cpu, hOn⟩
    have hARRother := H_jobs_come_from_arrival_sequence j_other t hSchedOther
    have hFP := H_respects_FP_policy j j_other cpu t H_j_arrives hBack hOn hCE
    have hDIFF :=
      bertogna_fp_interference_by_different_tasks task_cost task_period task_deadline
        job_arrival job_cost job_deadline job_task arr_seq H_sporadic_tasks
        H_valid_job_parameters ts H_valid_task_parameters
        H_constrained_deadlines H_all_jobs_from_taskset
        (num_cpus := num_cpus) alpha sched H_jobs_come_from_arrival_sequence
        H_sequential_jobs H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
        higher_eq_priority H_respects_affinity H_work_conserving H_respects_FP_policy
        tsk task_in_ts alpha' H_affinity_subset H_at_least_one_cpu hp_bounds
        H_response_time_of_interfering_tasks_is_known H_hp_bounds_has_interfering_tasks
        H_response_time_bounds_ge_cost H_interfering_tasks_miss_no_deadlines R
        H_response_time_recurrence_holds H_response_time_no_larger_than_deadline
        j H_j_arrives H_job_of_tsk H_j_not_completed H_previous_jobs_of_tsk_completed
        t j_other ⟨ht.1, ht.2⟩ hARRother hBack hSchedOther
    have hAPA := H_respects_affinity j_other cpu t hOn
    refine ⟨j_other, hSch, ?_, ?_⟩
    · rw [hp_def, List.mem_filter]
      exact ⟨H_all_jobs_from_taskset j_other hARRother, decide_eq_true_eq.mpr
        ⟨by rw [H_job_of_tsk] at hFP; exact hFP, hDIFF, ⟨cpu, hcpu, hAPA⟩⟩⟩
    · show decide (task_scheduled_on_affinity job_task sched (alpha tsk)
        (job_task j_other) t) = true
      exact decide_eq_true_eq.mpr ⟨cpu, hAlpha, by
        unfold task_scheduled_on; rw [hSch]; simp⟩
  -- Define total function: for each cpu, pick the scheduled job (if in alpha') or j
  let j_of : Fin num_cpus → Job := fun cpu =>
    if h : cpu ∈ alpha' tsk then (hAssign cpu h).choose else j
  let g : Fin num_cpus → sporadic_task := fun cpu => job_task (j_of cpu)
  -- Properties of g for cpu in alpha'(tsk)
  have hg_spec : ∀ cpu (hcpu : cpu ∈ alpha' tsk),
      sched cpu t = some (j_of cpu) ∧ g cpu ∈ hp ∧ p (g cpu) = true := by
    intro cpu hcpu
    have hj_eq : j_of cpu = (hAssign cpu hcpu).choose := by
      show (if h : cpu ∈ alpha' tsk then _ else _) = _; exact dif_pos hcpu
    have spec := (hAssign cpu hcpu).choose_spec
    exact ⟨by rw [hj_eq]; exact spec.1,
           by show job_task (j_of cpu) ∈ hp; rw [hj_eq]; exact spec.2.1,
           by show p (job_task (j_of cpu)) = true; rw [hj_eq]; exact spec.2.2⟩
  -- Injectivity of g on alpha'(tsk)
  have hInj : Set.InjOn g ↑(alpha' tsk) := by
    intro cpu1 h1 cpu2 h2 hEq
    have spec1 := hg_spec cpu1 h1
    have spec2 := hg_spec cpu2 h2
    have hSched1 : scheduled sched (j_of cpu1) t :=
      ⟨cpu1, by unfold scheduled_on; rw [spec1.1]; simp⟩
    have hSched2 : scheduled sched (j_of cpu2) t :=
      ⟨cpu2, by unfold scheduled_on; rw [spec2.1]; simp⟩
    have hPend1 := scheduled_implies_pending job_arrival job_cost sched (j_of cpu1)
      H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute t hSched1
    have hPend2 := scheduled_implies_pending job_arrival job_cost sched (j_of cpu2)
      H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute t hSched2
    have hArr1 := H_jobs_come_from_arrival_sequence (j_of cpu1) t hSched1
    have hArr2 := H_jobs_come_from_arrival_sequence (j_of cpu2) t hSched2
    -- Derive HP status with alpha (from alpha' filter membership)
    have hHP1 : higher_priority_task_in alpha higher_eq_priority tsk
        (alpha tsk) (g cpu1) := by
      obtain ⟨hPri, hNeq, hInter⟩ := of_decide_eq_true (List.mem_filter.mp spec1.2.1).2
      exact ⟨hPri, hNeq, let ⟨c, hc1, hc2⟩ := hInter; ⟨c, hSub' c hc1, hc2⟩⟩
    -- Same job by sporadic model
    have hEqJob : j_of cpu1 = j_of cpu2 := by
      by_contra hDiff
      by_cases harr : job_arrival (j_of cpu1) ≤ job_arrival (j_of cpu2)
      · have SPO := H_sporadic_tasks (j_of cpu1) (j_of cpu2) hDiff hArr1 hArr2
          (show job_task (j_of cpu1) = job_task (j_of cpu2) from hEq) harr
        exact hPend1.2 (completion_monotonic job_cost sched (j_of cpu1)
          H_completed_jobs_dont_execute _ _ (le_trans SPO hPend2.1)
          (hPrevHP (j_of cpu1) hArr1 hHP1))
      · push_neg at harr
        have hHP2 : higher_priority_task_in alpha higher_eq_priority tsk
            (alpha tsk) (g cpu2) := by rw [← show g cpu1 = g cpu2 from hEq]; exact hHP1
        have SPO := H_sporadic_tasks (j_of cpu2) (j_of cpu1) (Ne.symm hDiff) hArr2 hArr1
          (show job_task (j_of cpu2) = job_task (j_of cpu1) from hEq.symm) (le_of_lt harr)
        exact hPend2.2 (completion_monotonic job_cost sched (j_of cpu2)
          H_completed_jobs_dont_execute _ _ (le_trans SPO hPend1.1)
          (hPrevHP (j_of cpu2) hArr2 hHP2))
    exact H_sequential_jobs (j_of cpu1) t cpu1 cpu2 spec1.1 (by rw [hEqJob]; exact spec2.1)
  -- Counting: countP p hp ≥ alpha'.card
  have hHpNodup : hp.Nodup := H_ts_nodup.filter _
  have hFilterNodup : (hp.filter p).Nodup := hHpNodup.filter _
  rw [List.countP_eq_length_filter, ← List.toFinset_card_of_nodup hFilterNodup]
  exact Finset.card_le_card_of_injOn g
    (fun cpu hcpu => List.mem_toFinset.mpr
      (List.mem_filter.mpr ⟨(hg_spec cpu hcpu).2.1, (hg_spec cpu hcpu).2.2⟩))
    hInj

include H_sporadic_tasks H_valid_job_parameters H_valid_task_parameters H_constrained_deadlines H_all_jobs_from_taskset H_jobs_come_from_arrival_sequence H_sequential_jobs H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_respects_affinity H_work_conserving H_respects_FP_policy H_affinity_subset H_at_least_one_cpu H_response_time_of_interfering_tasks_is_known H_hp_bounds_has_interfering_tasks H_response_time_bounds_ge_cost H_interfering_tasks_miss_no_deadlines H_response_time_recurrence_holds H_response_time_no_larger_than_deadline H_j_arrives H_job_of_tsk H_j_not_completed H_previous_jobs_of_tsk_completed in
set_option maxHeartbeats 800000 in
theorem bertogna_fp_interference_in_non_full_processors :
    ∀ delta,
      let hp_tasks := ts.filter (fun tsk_other =>
        decide (higher_priority_task_in alpha higher_eq_priority tsk (alpha' tsk) tsk_other))
      let x_val := fun i => task_interference job_arrival job_cost job_task sched alpha j i
        (job_arrival j) (job_arrival j + R)
      let num_exceeding := hp_tasks.countP (fun i => decide (x_val i ≥ delta))
      0 < num_exceeding ∧ num_exceeding < (alpha' tsk).card →
      ((hp_tasks.filter (fun i => decide (x_val i < delta))).map x_val).sum ≥
      delta * ((alpha' tsk).card - num_exceeding) := by
  intro delta hp_tasks x_val num_exceeding ⟨hHAS, hLT⟩
  set hpE := hp_tasks.filter (fun i => decide (x_val i ≥ delta)) with hpE_def
  set hpL := hp_tasks.filter (fun i => decide (x_val i < delta)) with hpL_def
  set k := hpE.length with k_def
  have hkEq : num_exceeding = k := by
    simp only [k_def, hpE_def]
    exact List.countP_eq_length_filter
  rw [hkEq] at hHAS hLT; rw [hkEq]
  set TI := total_interference job_arrival job_cost sched j
    (job_arrival j) (job_arrival j + R) with TI_def
  -- Step 1: Σ_hp x ≥ TI * |α'|
  have hSubBusy :=
    bertogna_fp_all_cpus_in_subaffinity_busy
      task_cost task_period task_deadline job_arrival job_cost job_deadline job_task
      arr_seq H_sporadic_tasks H_valid_job_parameters ts H_valid_task_parameters
      H_constrained_deadlines H_all_jobs_from_taskset (num_cpus := num_cpus) alpha sched
      H_jobs_come_from_arrival_sequence H_sequential_jobs H_jobs_must_arrive_to_execute
      H_completed_jobs_dont_execute higher_eq_priority H_respects_affinity
      H_work_conserving H_respects_FP_policy tsk task_in_ts alpha'
      H_affinity_subset H_at_least_one_cpu hp_bounds
      H_response_time_of_interfering_tasks_is_known H_hp_bounds_has_interfering_tasks
      H_response_time_bounds_ge_cost H_interfering_tasks_miss_no_deadlines R
      H_response_time_recurrence_holds H_response_time_no_larger_than_deadline
      j H_j_arrives H_job_of_tsk H_j_not_completed H_previous_jobs_of_tsk_completed
  -- Step 2: HP completion
  have hPrevHP : ∀ j0,
      arrives_in arr_seq j0 →
      higher_priority_task_in alpha higher_eq_priority tsk (alpha tsk) (job_task j0) →
      completed job_cost sched j0 (job_arrival j0 + task_period (job_task j0)) := by
    intro j0 hA0 hHP0
    have hIn0 := H_all_jobs_from_taskset j0 hA0
    obtain ⟨R0, hR0⟩ := H_hp_bounds_has_interfering_tasks (job_task j0) hIn0 hHP0
    exact completion_monotonic job_cost sched j0 H_completed_jobs_dont_execute _ _ (by
      apply Nat.add_le_add_left
      exact le_trans (H_interfering_tasks_miss_no_deadlines _ R0 hR0)
        (H_constrained_deadlines _ hIn0))
      (H_response_time_of_interfering_tasks_is_known _ R0 hR0 j0 hA0 rfl)
  -- Step 3: hSingleLeTotal
  have hSingleLeTotal : ∀ i ∈ hp_tasks, x_val i ≤ TI := by
    intro i hi
    show task_interference job_arrival job_cost job_task sched alpha j i
          (job_arrival j) (job_arrival j + R) ≤
        total_interference job_arrival job_cost sched j
          (job_arrival j) (job_arrival j + R)
    simp only [Prosa.Classic.Model.Schedule.Apa.Interference.task_interference,
               Prosa.Classic.Model.Schedule.Apa.Interference.total_interference]
    apply Finset.sum_le_sum
    intro t' _
    by_cases hbl : backlogged job_arrival job_cost sched j t'
    · -- backlogged: simplify condition
      simp only [show (backlogged job_arrival job_cost sched j t') = True from eq_true hbl,
                  true_and, ite_true]
      -- Goal: Σ_cpu [if can_execute ∧ task_sched then 1 else 0] ≤ 1
      -- Goal: Σ_cpu [if can_execute ∧ task_sched then 1 else 0] ≤ 1
      by_cases hExists : ∃ cpu0 : Fin num_cpus,
          can_execute_on alpha (job_task j) cpu0 ∧
          task_scheduled_on job_task sched i cpu0 t' = true
      · obtain ⟨cpu0, hcan0, htso0⟩ := hExists
        suffices h : ∀ cpu, (if can_execute_on alpha (job_task j) cpu ∧
            task_scheduled_on job_task sched i cpu t' = true then (1:ℕ) else 0) =
            if cpu = cpu0 then 1 else 0 by
          simp_rw [h]
          rw [Finset.sum_ite_eq' Finset.univ cpu0 (fun _ => (1:ℕ))]
          simp
        intro cpu
        by_cases heq : cpu = cpu0
        · subst heq; simp [hcan0, htso0]
        · have hFalse : ¬(can_execute_on alpha (job_task j) cpu ∧
              task_scheduled_on job_task sched i cpu t' = true) := by
            intro ⟨_, htso'⟩
            unfold task_scheduled_on at htso0 htso'
            cases h0 : sched cpu0 t' with
            | none => simp [h0] at htso0
            | some j0 =>
              cases h1 : sched cpu t' with
              | none => simp [h1] at htso'
              | some j1 =>
                simp [h0] at htso0; simp [h1] at htso'
                have hSameTask : job_task j1 = job_task j0 := by rw [htso', htso0]
                have hSched0 : scheduled sched j0 t' :=
                  ⟨cpu0, by unfold scheduled_on; rw [h0]; simp⟩
                have hSched1 : scheduled sched j1 t' :=
                  ⟨cpu, by unfold scheduled_on; rw [h1]; simp⟩
                have hPend0 := scheduled_implies_pending job_arrival job_cost sched j0
                  H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute t' hSched0
                have hPend1 := scheduled_implies_pending job_arrival job_cost sched j1
                  H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute t' hSched1
                have hArr0 := H_jobs_come_from_arrival_sequence j0 t' hSched0
                have hArr1 := H_jobs_come_from_arrival_sequence j1 t' hSched1
                have hi_hp' := of_decide_eq_true (List.mem_filter.mp hi).2
                have hi_hp_alpha : higher_priority_task_in alpha higher_eq_priority tsk
                    (alpha tsk) i := by
                  obtain ⟨hPri, hNeq, hInter⟩ := hi_hp'
                  exact ⟨hPri, hNeq, let ⟨c, h1, h2⟩ := hInter;
                    ⟨c, H_affinity_subset tsk task_in_ts c h1, h2⟩⟩
                have hEqJob : j0 = j1 := by
                  by_contra hDiff
                  by_cases harr : job_arrival j0 ≤ job_arrival j1
                  · have SPO := H_sporadic_tasks j0 j1 hDiff hArr0 hArr1
                      (hSameTask.symm) harr
                    have hLE := le_trans SPO hPend1.1
                    have hComp := hPrevHP j0 hArr0 (by rwa [htso0])
                    exact hPend0.2 (completion_monotonic job_cost sched j0
                      H_completed_jobs_dont_execute _ _ hLE hComp)
                  · push_neg at harr
                    have SPO := H_sporadic_tasks j1 j0 (Ne.symm hDiff) hArr1 hArr0
                      hSameTask (le_of_lt harr)
                    have hLE := le_trans SPO hPend0.1
                    have hComp := hPrevHP j1 hArr1 (by rwa [htso'])
                    exact hPend1.2 (completion_monotonic job_cost sched j1
                      H_completed_jobs_dont_execute _ _ hLE hComp)
                cases hEqJob
                exact heq (H_sequential_jobs j0 t' cpu cpu0 h1 h0)
          simp [hFalse, heq]
      · have : ∀ cpu : Fin num_cpus,
            (if can_execute_on alpha (job_task j) cpu ∧
                task_scheduled_on job_task sched i cpu t' = true
              then (1:ℕ) else 0) = 0 := by
          intro cpu; exact if_neg (fun h => hExists ⟨cpu, h⟩)
        simp_rw [this]; simp
    · -- not backlogged
      simp [show ¬(backlogged job_arrival job_cost sched j t') from hbl]
  -- Step 4: Partition sum
  have hPartSum : (hp_tasks.map x_val).sum =
      (hpE.map x_val).sum + (hpL.map x_val).sum := by
    suffices ∀ L : List sporadic_task,
        (L.map x_val).sum =
        ((L.filter (fun i => decide (x_val i ≥ delta))).map x_val).sum +
        ((L.filter (fun i => decide (x_val i < delta))).map x_val).sum by
      exact this hp_tasks
    intro L; induction L with
    | nil => simp
    | cons hd tl ih =>
      simp only [List.map_cons, List.sum_cons, List.filter_cons]
      by_cases hge : x_val hd ≥ delta
      · have h1 : decide (x_val hd ≥ delta) = true := decide_eq_true_eq.mpr hge
        have h2 : decide (x_val hd < delta) = false := by
          simp only [decide_eq_false_iff_not, not_lt]; exact hge
        simp [h1, h2]
        simp only [GE.ge] at ih; omega
      · push_neg at hge
        have h1 : decide (x_val hd ≥ delta) = false := by
          simp only [decide_eq_false_iff_not, not_le]; exact hge
        have h2 : decide (x_val hd < delta) = true := decide_eq_true_eq.mpr hge
        simp [h1, h2]
        simp only [GE.ge] at ih; omega
  -- Step 5: Σ_hpE ≤ TI * k
  have hExceedingBound : (hpE.map x_val).sum ≤ TI * k := by
    suffices ∀ L : List sporadic_task, (∀ i ∈ L, x_val i ≤ TI) →
        (L.map x_val).sum ≤ TI * L.length by
      exact this hpE (fun i hi => hSingleLeTotal i (List.mem_of_mem_filter hi))
    intro L hpw; induction L with
    | nil => simp
    | cons hd tl ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.mul_succ]
      have h1 := hpw hd (by simp)
      have h2 := ih (fun i hi => hpw i (by simp [hi]))
      omega
  -- Step 6: TI ≥ delta
  have hTI_ge_delta : TI ≥ delta := by
    have hne : hpE ≠ [] := by
      intro h; simp only [k_def, h, List.length_nil] at hHAS; omega
    obtain ⟨tsk_a, hIn⟩ := List.exists_mem_of_ne_nil _ hne
    have hge : x_val tsk_a ≥ delta :=
      of_decide_eq_true (List.mem_filter.mp hIn).2
    exact le_trans hge (hSingleLeTotal tsk_a (List.mem_of_mem_filter hIn))
  -- Step 7: Combine
  change (hpL.map x_val).sum ≥ delta * ((alpha' tsk).card - k)
  have h_part : (hpE.map x_val).sum + (hpL.map x_val).sum = (hp_tasks.map x_val).sum := by
    omega
  have h_lb : (hp_tasks.map x_val).sum ≥ TI * (alpha' tsk).card := hSubBusy
  have h_ub : (hpE.map x_val).sum ≤ TI * k := hExceedingBound
  have hle : k ≤ (alpha' tsk).card := le_of_lt hLT
  have h_sub : TI * ((alpha' tsk).card - k) + TI * k = TI * (alpha' tsk).card := by
    rw [← Nat.left_distrib, Nat.sub_add_cancel hle]
  calc delta * ((alpha' tsk).card - k)
      ≤ TI * ((alpha' tsk).card - k) := Nat.mul_le_mul_right _ hTI_ge_delta
    _ ≤ (hpL.map x_val).sum := by omega

include H_sporadic_tasks H_valid_job_parameters H_valid_task_parameters H_constrained_deadlines H_all_jobs_from_taskset H_jobs_come_from_arrival_sequence H_sequential_jobs H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_respects_affinity H_work_conserving H_respects_FP_policy H_affinity_subset H_at_least_one_cpu H_response_time_of_interfering_tasks_is_known H_hp_bounds_has_interfering_tasks H_response_time_bounds_ge_cost H_interfering_tasks_miss_no_deadlines H_response_time_recurrence_holds H_response_time_no_larger_than_deadline H_j_arrives H_job_of_tsk H_j_not_completed H_previous_jobs_of_tsk_completed in
theorem bertogna_fp_minimum_exceeds_interference :
    ∀ delta,
      ((ts.filter (fun tsk_other =>
        decide (higher_priority_task_in alpha higher_eq_priority tsk (alpha' tsk) tsk_other))).map
        (fun tsk_k => task_interference job_arrival job_cost job_task sched alpha j tsk_k
          (job_arrival j) (job_arrival j + R))).sum ≥
      delta * (alpha' tsk).card →
      ((ts.filter (fun tsk_other =>
        decide (higher_priority_task_in alpha higher_eq_priority tsk (alpha' tsk) tsk_other))).map
        (fun tsk_k => min (task_interference job_arrival job_cost job_task sched alpha j tsk_k
          (job_arrival j) (job_arrival j + R)) delta)).sum ≥
      delta * (alpha' tsk).card := by
  intro delta hSum
  set hp : List sporadic_task :=
    ts.filter (fun t => decide (higher_priority_task_in alpha higher_eq_priority tsk (alpha' tsk) t))
    with hp_def
  set xval : sporadic_task → ℕ := fun tsk_k =>
    task_interference job_arrival job_cost job_task sched alpha j tsk_k
      (job_arrival j) (job_arrival j + R) with xval_def
  change (hp.map xval).sum ≥ delta * (alpha' tsk).card at hSum
  change (hp.map (fun i => min (xval i) delta)).sum ≥ delta * (alpha' tsk).card
  -- Generic partition lemma
  have hPart : ∀ (L : List sporadic_task) (g : sporadic_task → ℕ),
      (L.map g).sum =
      ((L.filter (fun i => decide (delta ≤ xval i))).map g).sum +
      ((L.filter (fun i => decide (xval i < delta))).map g).sum := by
    intro L g
    induction L with
    | nil => simp
    | cons hd tl ih =>
      by_cases h : delta ≤ xval hd
      · have hE : List.filter (fun i => decide (delta ≤ xval i)) (hd :: tl)
                  = hd :: List.filter (fun i => decide (delta ≤ xval i)) tl := by
          simp [h]
        have hL : List.filter (fun i => decide (xval i < delta)) (hd :: tl)
                  = List.filter (fun i => decide (xval i < delta)) tl := by
          simp [not_lt.mpr h]
        rw [List.map_cons, List.sum_cons, hE, hL, List.map_cons, List.sum_cons, ih]
        ac_rfl
      · have hE : List.filter (fun i => decide (delta ≤ xval i)) (hd :: tl)
                  = List.filter (fun i => decide (delta ≤ xval i)) tl := by
          simp [h]
        have hL : List.filter (fun i => decide (xval i < delta)) (hd :: tl)
                  = hd :: List.filter (fun i => decide (xval i < delta)) tl := by
          simp [Nat.lt_of_not_le h]
        rw [List.map_cons, List.sum_cons, hE, hL, List.map_cons, List.sum_cons, ih]
        ac_rfl
  have hSumSplit := hPart hp xval
  have hMinSplit := hPart hp (fun i => min (xval i) delta)
  set hpE : List sporadic_task := hp.filter (fun i => decide (delta ≤ xval i)) with hpE_def
  set hpL : List sporadic_task := hp.filter (fun i => decide (xval i < delta)) with hpL_def
  set k := hpE.length
  -- On hpE, xval ≥ delta, so min (xval i) delta = delta
  have hEmin_eq :
      (hpE.map (fun i => min (xval i) delta)) =
      hpE.map (fun _ => delta) := by
    apply List.map_congr_left
    intro i hi
    have hmem : i ∈ hp ∧ decide (delta ≤ xval i) = true := by
      simpa [hpE_def, List.mem_filter] using hi
    have hle : delta ≤ xval i := of_decide_eq_true hmem.2
    exact min_eq_right hle
  -- On hpL, xval < delta, so min (xval i) delta = xval i
  have hLmin_eq :
      (hpL.map (fun i => min (xval i) delta)) = hpL.map xval := by
    apply List.map_congr_left
    intro i hi
    have hmem : i ∈ hp ∧ decide (xval i < delta) = true := by
      simpa [hpL_def, List.mem_filter] using hi
    have hlt : xval i < delta := of_decide_eq_true hmem.2
    exact min_eq_left (le_of_lt hlt)
  have hEsum : (hpE.map (fun _ => delta)).sum = delta * k := by
    show (hpE.map (fun _ : sporadic_task => delta)).sum = delta * hpE.length
    rw [List.map_const', List.sum_replicate, smul_eq_mul, Nat.mul_comm]
  have hESum_xval_ge : (hpE.map xval).sum ≥ delta * k := by
    have hpw : ∀ i ∈ hpE, delta ≤ xval i := by
      intro i hi
      have : i ∈ hp ∧ decide (delta ≤ xval i) = true := by
        simpa [hpE_def, List.mem_filter] using hi
      exact of_decide_eq_true this.2
    show delta * k ≤ _
    simp only [k]
    suffices h : ∀ (L : List sporadic_task), (∀ i ∈ L, delta ≤ xval i) →
        delta * L.length ≤ (L.map xval).sum from h hpE hpw
    intro L hL
    induction L with
    | nil => simp
    | cons hd tl ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.mul_succ]
      have h1 : delta ≤ xval hd := hL hd (by simp)
      have h2 := ih (fun i hi => hL i (by simp [hi]))
      linarith
  -- 3-case analysis
  rw [hMinSplit, hEmin_eq, hEsum, hLmin_eq]
  rcases Nat.lt_or_ge k (alpha' tsk).card with hLT | hGE
  · rcases Nat.eq_zero_or_pos k with hZ | hPos
    · -- Case 1: k = 0
      have hpE_nil : hpE = [] := List.length_eq_zero_iff.mp hZ
      have hESum_zero : (hpE.map xval).sum = 0 := by rw [hpE_nil]; simp
      have : (hpL.map xval).sum = (hp.map xval).sum := by
        rw [hSumSplit, hESum_zero]; ring
      rw [this]
      simp [hZ]
      exact hSum
    · -- Case 3: 0 < k < |α'|
      have hNFP :=
        bertogna_fp_interference_in_non_full_processors task_cost task_period task_deadline
          job_arrival job_cost job_deadline job_task arr_seq H_sporadic_tasks
          H_valid_job_parameters ts H_valid_task_parameters H_constrained_deadlines
          H_all_jobs_from_taskset (num_cpus := num_cpus) alpha sched
          H_jobs_come_from_arrival_sequence H_sequential_jobs H_jobs_must_arrive_to_execute
          H_completed_jobs_dont_execute higher_eq_priority H_respects_affinity
          H_work_conserving H_respects_FP_policy tsk task_in_ts alpha'
          H_affinity_subset H_at_least_one_cpu hp_bounds
          H_response_time_of_interfering_tasks_is_known H_hp_bounds_has_interfering_tasks
          H_response_time_bounds_ge_cost H_interfering_tasks_miss_no_deadlines R
          H_response_time_recurrence_holds H_response_time_no_larger_than_deadline
          j H_j_arrives H_job_of_tsk H_j_not_completed H_previous_jobs_of_tsk_completed
          delta
      -- The let-bound version needs massaging; use `show` or `change`
      have hCountP_eq : hp.countP (fun i => decide (xval i ≥ delta)) = k := by
        simp only [k, hpE_def]
        rw [List.countP_eq_length_filter]
      have hCond : 0 < hp.countP (fun i => decide (xval i ≥ delta)) ∧
          hp.countP (fun i => decide (xval i ≥ delta)) < (alpha' tsk).card := by
        rw [hCountP_eq]; exact ⟨hPos, hLT⟩
      have hNFP' := hNFP hCond
      have hFilter_eq : (hp.filter (fun i => decide (xval i < delta))) = hpL := rfl
      rw [hFilter_eq] at hNFP'
      rw [hCountP_eq] at hNFP'
      have hsum_eq : delta * k + delta * ((alpha' tsk).card - k) = delta * (alpha' tsk).card := by
        rw [← Nat.mul_add, Nat.add_sub_cancel' (le_of_lt hLT)]
      linarith
  · -- Case 2: k ≥ |α'|
    have : delta * (alpha' tsk).card ≤ delta * k := Nat.mul_le_mul_left delta hGE
    linarith [Nat.zero_le ((hpL.map xval).sum)]

include H_sporadic_tasks H_valid_job_parameters H_valid_task_parameters H_constrained_deadlines H_all_jobs_from_taskset H_jobs_come_from_arrival_sequence H_sequential_jobs H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_respects_affinity H_work_conserving H_respects_FP_policy H_affinity_subset H_at_least_one_cpu H_response_time_of_interfering_tasks_is_known H_hp_bounds_has_interfering_tasks H_response_time_bounds_ge_cost H_interfering_tasks_miss_no_deadlines H_response_time_recurrence_holds H_response_time_no_larger_than_deadline H_j_arrives H_job_of_tsk H_j_not_completed H_previous_jobs_of_tsk_completed H_ts_nodup in
theorem bertogna_fp_interference_on_subaffinity :
    ∀ delta,
      ((ts.filter (fun tsk_other =>
        decide (higher_priority_task_in alpha higher_eq_priority tsk (alpha tsk) tsk_other))).map
        (fun tsk_k => task_interference job_arrival job_cost job_task sched alpha j tsk_k
          (job_arrival j) (job_arrival j + R))).sum ≥
      delta * (alpha tsk).card →
      ((ts.filter (fun tsk_other =>
        decide (higher_priority_task_in alpha higher_eq_priority tsk (alpha' tsk) tsk_other))).map
        (fun tsk_k => task_interference job_arrival job_cost job_task sched alpha j tsk_k
          (job_arrival j) (job_arrival j + R))).sum ≥
      delta * (alpha' tsk).card := by
  intro delta hLE
  set X := total_interference job_arrival job_cost sched j
              (job_arrival j) (job_arrival j + R)
  -- all_cpus_in_affinity_busy (sorry): sum(α-filter) = X * |α|
  have hAll :=
    bertogna_fp_all_cpus_in_affinity_busy
      task_cost task_period task_deadline job_arrival job_cost job_deadline job_task
      arr_seq H_sporadic_tasks H_valid_job_parameters ts H_valid_task_parameters
      H_constrained_deadlines H_all_jobs_from_taskset H_ts_nodup (num_cpus := num_cpus) alpha sched
      H_jobs_come_from_arrival_sequence H_sequential_jobs H_jobs_must_arrive_to_execute
      H_completed_jobs_dont_execute higher_eq_priority H_respects_affinity
      H_work_conserving H_respects_FP_policy tsk task_in_ts alpha'
      H_affinity_subset H_at_least_one_cpu hp_bounds
      H_response_time_of_interfering_tasks_is_known H_hp_bounds_has_interfering_tasks
      H_response_time_bounds_ge_cost H_interfering_tasks_miss_no_deadlines R
      H_response_time_recurrence_holds H_response_time_no_larger_than_deadline
      j H_j_arrives H_job_of_tsk H_j_not_completed H_previous_jobs_of_tsk_completed
  -- all_cpus_in_subaffinity_busy (sorry): sum(α'-filter) ≥ X * |α'|
  have hSub :=
    bertogna_fp_all_cpus_in_subaffinity_busy
      task_cost task_period task_deadline job_arrival job_cost job_deadline job_task
      arr_seq H_sporadic_tasks H_valid_job_parameters ts H_valid_task_parameters
      H_constrained_deadlines H_all_jobs_from_taskset (num_cpus := num_cpus) alpha sched
      H_jobs_come_from_arrival_sequence H_sequential_jobs H_jobs_must_arrive_to_execute
      H_completed_jobs_dont_execute higher_eq_priority H_respects_affinity
      H_work_conserving H_respects_FP_policy tsk task_in_ts alpha'
      H_affinity_subset H_at_least_one_cpu hp_bounds
      H_response_time_of_interfering_tasks_is_known H_hp_bounds_has_interfering_tasks
      H_response_time_bounds_ge_cost H_interfering_tasks_miss_no_deadlines R
      H_response_time_recurrence_holds H_response_time_no_larger_than_deadline
      j H_j_arrives H_job_of_tsk H_j_not_completed H_previous_jobs_of_tsk_completed
  -- From hAll + hLE: X * |α| ≥ delta * |α|
  rw [hAll] at hLE
  -- Since |α'| > 0 and α' ⊆ α, |α| > 0
  have hAlphaPos : (alpha tsk).card > 0 := by
    have hSub' := H_affinity_subset tsk task_in_ts
    have hAlpha'Pos := H_at_least_one_cpu tsk task_in_ts
    exact Nat.lt_of_lt_of_le hAlpha'Pos (leq_subaffinity (alpha' tsk) (alpha tsk) hSub')
  -- X ≥ delta
  have hXge : X ≥ delta := Nat.le_of_mul_le_mul_right hLE hAlphaPos
  -- sum(α') ≥ X * |α'| ≥ delta * |α'|
  exact le_trans (Nat.mul_le_mul_right _ hXge) hSub

include H_sporadic_tasks H_valid_job_parameters H_valid_task_parameters H_constrained_deadlines H_all_jobs_from_taskset H_jobs_come_from_arrival_sequence H_sequential_jobs H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_respects_affinity H_work_conserving H_respects_FP_policy H_affinity_subset H_at_least_one_cpu H_response_time_of_interfering_tasks_is_known H_hp_bounds_has_interfering_tasks H_response_time_bounds_ge_cost H_interfering_tasks_miss_no_deadlines H_response_time_recurrence_holds H_response_time_no_larger_than_deadline H_j_arrives H_job_of_tsk H_j_not_completed H_previous_jobs_of_tsk_completed H_ts_nodup in
theorem bertogna_fp_sum_exceeds_total_interference :
    ((hp_bounds.filter (fun tsk_R =>
      decide (higher_priority_task_in alpha higher_eq_priority tsk (alpha' tsk) tsk_R.1))).map
      (fun tsk_R => min (task_interference job_arrival job_cost job_task sched alpha j tsk_R.1
        (job_arrival j) (job_arrival j + R))
        (R - task_cost tsk + 1))).sum >
    total_interference_bound_fp task_cost task_period alpha tsk
      (alpha' tsk) hp_bounds R higher_eq_priority := by
  set x : sporadic_task → ℕ := fun k =>
    task_interference job_arrival job_cost job_task sched alpha j k
      (job_arrival j) (job_arrival j + R) with x_def
  set c := task_cost tsk with c_def
  set delta := R - c + 1 with delta_def
  set N := total_interference_bound_fp task_cost task_period alpha tsk
    (alpha' tsk) hp_bounds R higher_eq_priority with N_def
  set hp_tasks := ts.filter (fun t =>
    decide (higher_priority_task_in alpha higher_eq_priority tsk (alpha' tsk) t)) with hp_tasks_def
  -- Step A: From recurrence, N < delta * |α'|
  have hRec : R = c + N / (alpha' tsk).card := by
    have h := H_response_time_recurrence_holds
    unfold div_floor at h; exact h
  have hCleR : c ≤ R := by rw [hRec]; exact Nat.le_add_right _ _
  have hAlpha'Pos : (alpha' tsk).card > 0 := H_at_least_one_cpu tsk task_in_ts
  have hDivEq : N / (alpha' tsk).card = R - c := by
    rw [hRec, Nat.add_sub_cancel_left]
  have hNlt : N < delta * (alpha' tsk).card := by
    have hmod := Nat.div_add_mod N (alpha' tsk).card
    rw [Nat.mul_comm] at hmod
    have hmod' : N % (alpha' tsk).card < (alpha' tsk).card :=
      Nat.mod_lt N hAlpha'Pos
    have hDelta_eq : delta = N / (alpha' tsk).card + 1 := by
      rw [delta_def, hDivEq]
    rw [hDelta_eq, Nat.add_mul, Nat.one_mul]
    omega
  -- Step B: ALLBUSY — sum over hp_tasks of x_k ≥ X * |α'|
  -- From all_cpus_in_affinity_busy: sum(α-filter) = X * |α|
  -- From too_much_interference: X ≥ delta = R - c + 1
  -- From interference_on_subaffinity: sum(α'-filter) ≥ delta * |α'|
  set X := total_interference job_arrival job_cost sched j
              (job_arrival j) (job_arrival j + R) with X_def
  have hTooMuch : X ≥ delta :=
    bertogna_fp_too_much_interference
      task_cost task_period task_deadline job_arrival job_cost job_deadline job_task
      arr_seq H_sporadic_tasks H_valid_job_parameters ts H_valid_task_parameters
      H_constrained_deadlines H_all_jobs_from_taskset (num_cpus := num_cpus) alpha sched
      H_jobs_come_from_arrival_sequence H_sequential_jobs H_jobs_must_arrive_to_execute
      H_completed_jobs_dont_execute higher_eq_priority H_respects_affinity
      H_work_conserving H_respects_FP_policy tsk task_in_ts alpha'
      H_affinity_subset H_at_least_one_cpu hp_bounds
      H_response_time_of_interfering_tasks_is_known H_hp_bounds_has_interfering_tasks
      H_response_time_bounds_ge_cost H_interfering_tasks_miss_no_deadlines R
      H_response_time_recurrence_holds H_response_time_no_larger_than_deadline
      j H_j_arrives H_job_of_tsk H_j_not_completed H_previous_jobs_of_tsk_completed
  have hAllBusy :=
    bertogna_fp_all_cpus_in_affinity_busy
      task_cost task_period task_deadline job_arrival job_cost job_deadline job_task
      arr_seq H_sporadic_tasks H_valid_job_parameters ts H_valid_task_parameters
      H_constrained_deadlines H_all_jobs_from_taskset H_ts_nodup (num_cpus := num_cpus) alpha sched
      H_jobs_come_from_arrival_sequence H_sequential_jobs H_jobs_must_arrive_to_execute
      H_completed_jobs_dont_execute higher_eq_priority H_respects_affinity
      H_work_conserving H_respects_FP_policy tsk task_in_ts alpha'
      H_affinity_subset H_at_least_one_cpu hp_bounds
      H_response_time_of_interfering_tasks_is_known H_hp_bounds_has_interfering_tasks
      H_response_time_bounds_ge_cost H_interfering_tasks_miss_no_deadlines R
      H_response_time_recurrence_holds H_response_time_no_larger_than_deadline
      j H_j_arrives H_job_of_tsk H_j_not_completed H_previous_jobs_of_tsk_completed
  have hSumHP_ge : (hp_tasks.map x).sum ≥ delta * (alpha' tsk).card :=
    bertogna_fp_interference_on_subaffinity
      task_cost task_period task_deadline job_arrival job_cost job_deadline job_task
      arr_seq H_sporadic_tasks H_valid_job_parameters ts H_valid_task_parameters
      H_constrained_deadlines H_all_jobs_from_taskset H_ts_nodup (num_cpus := num_cpus) alpha sched
      H_jobs_come_from_arrival_sequence H_sequential_jobs H_jobs_must_arrive_to_execute
      H_completed_jobs_dont_execute higher_eq_priority H_respects_affinity
      H_work_conserving H_respects_FP_policy tsk task_in_ts alpha'
      H_affinity_subset H_at_least_one_cpu hp_bounds
      H_response_time_of_interfering_tasks_is_known H_hp_bounds_has_interfering_tasks
      H_response_time_bounds_ge_cost H_interfering_tasks_miss_no_deadlines R
      H_response_time_recurrence_holds H_response_time_no_larger_than_deadline
      j H_j_arrives H_job_of_tsk H_j_not_completed H_previous_jobs_of_tsk_completed
      delta (by rw [hAllBusy]; exact Nat.mul_le_mul_right _ hTooMuch)
  -- Step C: Apply minimum_exceeds_interference
  have hMinHP : (hp_tasks.map (fun t => min (x t) delta)).sum ≥
      delta * (alpha' tsk).card :=
    bertogna_fp_minimum_exceeds_interference
      task_cost task_period task_deadline job_arrival job_cost job_deadline job_task
      arr_seq H_sporadic_tasks H_valid_job_parameters ts H_valid_task_parameters
      H_constrained_deadlines H_all_jobs_from_taskset (num_cpus := num_cpus) alpha sched
      H_jobs_come_from_arrival_sequence H_sequential_jobs H_jobs_must_arrive_to_execute
      H_completed_jobs_dont_execute higher_eq_priority H_respects_affinity
      H_work_conserving H_respects_FP_policy tsk task_in_ts alpha'
      H_affinity_subset H_at_least_one_cpu hp_bounds
      H_response_time_of_interfering_tasks_is_known H_hp_bounds_has_interfering_tasks
      H_response_time_bounds_ge_cost H_interfering_tasks_miss_no_deadlines R
      H_response_time_recurrence_holds H_response_time_no_larger_than_deadline
      j H_j_arrives H_job_of_tsk H_j_not_completed H_previous_jobs_of_tsk_completed
      delta hSumHP_ge
  -- Step D: Bridge hp_bounds → hp_tasks via witness injection
  have hp_tasks_nodup : hp_tasks.Nodup := List.Nodup.filter _ H_ts_nodup
  have hHas : ∀ t ∈ hp_tasks, ∃ R', (t, R') ∈ hp_bounds := by
    intro t ht
    rw [hp_tasks_def, List.mem_filter] at ht
    have h_hp_in_alpha' := of_decide_eq_true ht.2
    -- higher_priority_task_in alpha hep tsk (alpha' tsk) t
    -- implies higher_priority_task_in alpha hep tsk (alpha tsk) t
    -- because α' ⊆ α means affinity_intersects (alpha' tsk) (alpha t) →
    --   affinity_intersects (alpha tsk) (alpha t)
    have h_hp_in_alpha :
        higher_priority_task_in alpha higher_eq_priority tsk (alpha tsk) t := by
      obtain ⟨hPri, hNeq, hInter⟩ := h_hp_in_alpha'
      refine ⟨hPri, hNeq, ?_⟩
      -- affinity_intersects (alpha' tsk) (alpha t) → affinity_intersects (alpha tsk) (alpha t)
      obtain ⟨cpu, hIn1, hIn2⟩ := hInter
      exact ⟨cpu, H_affinity_subset tsk task_in_ts cpu hIn1, hIn2⟩
    exact H_hp_bounds_has_interfering_tasks t ht.1 h_hp_in_alpha
  choose pickR hPickMem using hHas
  let witList : List (sporadic_task × Time) :=
    hp_tasks.attach.map (fun ⟨t, ht⟩ => (t, pickR t ht))
  have hWit_nodup : witList.Nodup := by
    apply List.Nodup.map_on
    · intro ⟨a, ha⟩ _ ⟨b, hb⟩ _ hEq
      have : a = b := (Prod.mk.injEq _ _ _ _).mp hEq |>.1
      exact Subtype.ext this
    · exact (List.nodup_attach).mpr hp_tasks_nodup
  have hWit_sub : witList ⊆ hp_bounds := by
    intro p hp
    rcases List.mem_map.mp hp with ⟨⟨t, ht⟩, _, heq⟩
    rw [← heq]; exact hPickMem t ht
  -- All elements of witList satisfy the hp_task_in filter on alpha'
  have hWit_filtered : ∀ p ∈ witList,
      decide (higher_priority_task_in alpha higher_eq_priority tsk (alpha' tsk) p.1) = true := by
    intro p hp
    rcases List.mem_map.mp hp with ⟨⟨t, ht⟩, _, heq⟩
    rw [← heq]; simp
    rw [hp_tasks_def, List.mem_filter] at ht
    exact of_decide_eq_true ht.2
  -- sum over witList of g = sum over hp_tasks of g
  have hWit_sum :
      (witList.map (fun p => min (x p.1) delta)).sum =
      (hp_tasks.map (fun t => min (x t) delta)).sum := by
    show ((hp_tasks.attach.map _).map _).sum = _
    rw [List.map_map]
    conv_rhs => rw [show hp_tasks = hp_tasks.attach.map (·.val) from
      (hp_tasks.attach_map_subtype_val).symm]
    rw [List.map_map]
    rfl
  -- Multiset ≤: witList ⊆ hp_bounds as multisets
  have hMs : (↑witList : Multiset (sporadic_task × Time)) ≤ (↑hp_bounds : Multiset _) := by
    rw [Multiset.coe_le]
    exact hWit_nodup.subperm hWit_sub
  -- witList also ⊆ filtered hp_bounds (since all elements pass the filter)
  set hp_bounds_filt := hp_bounds.filter (fun tsk_R =>
    decide (higher_priority_task_in alpha higher_eq_priority tsk (alpha' tsk) tsk_R.1))
    with hp_bounds_filt_def
  have hWit_sub_filt : witList ⊆ hp_bounds_filt := by
    intro p hp
    rw [hp_bounds_filt_def, List.mem_filter]
    exact ⟨hWit_sub hp, hWit_filtered p hp⟩
  have hMs_filt : (↑witList : Multiset (sporadic_task × Time)) ≤
      (↑hp_bounds_filt : Multiset _) := by
    rw [Multiset.coe_le]
    exact hWit_nodup.subperm hWit_sub_filt
  have hBridge :
      (hp_tasks.map (fun t => min (x t) delta)).sum ≤
      (hp_bounds_filt.map (fun p : sporadic_task × Time => min (x p.1) delta)).sum := by
    rw [← hWit_sum]
    show (Multiset.map (fun p : sporadic_task × Time => min (x p.1) delta)
            (↑witList : Multiset (sporadic_task × Time))).sum ≤
         (Multiset.map (fun p : sporadic_task × Time => min (x p.1) delta)
            (↑hp_bounds_filt : Multiset (sporadic_task × Time))).sum
    have hSplit : (↑hp_bounds_filt : Multiset (sporadic_task × Time)) =
        (↑witList : Multiset (sporadic_task × Time)) +
          ((↑hp_bounds_filt : Multiset (sporadic_task × Time)) -
           (↑witList : Multiset (sporadic_task × Time))) := by
      exact (tsub_add_cancel_of_le hMs_filt).symm.trans (add_comm _ _)
    rw [hSplit, Multiset.map_add, Multiset.sum_add]
    exact Nat.le_add_right _ _
  -- Final: sum_hp_bounds_filt ≥ sum_hp_tasks min ≥ delta * |α'| > N
  calc (hp_bounds_filt.map (fun tsk_R => min (x tsk_R.1) delta)).sum
      ≥ (hp_tasks.map (fun t => min (x t) delta)).sum := hBridge
    _ ≥ delta * (alpha' tsk).card := hMinHP
    _ > N := hNlt

include H_sporadic_tasks H_valid_job_parameters H_valid_task_parameters H_constrained_deadlines H_all_jobs_from_taskset H_jobs_come_from_arrival_sequence H_sequential_jobs H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_respects_affinity H_work_conserving H_respects_FP_policy H_affinity_subset H_at_least_one_cpu H_response_time_of_interfering_tasks_is_known H_hp_bounds_has_interfering_tasks H_response_time_bounds_ge_cost H_interfering_tasks_miss_no_deadlines H_response_time_recurrence_holds H_response_time_no_larger_than_deadline H_j_arrives H_job_of_tsk H_j_not_completed H_previous_jobs_of_tsk_completed H_ts_nodup in
theorem bertogna_fp_exists_task_that_exceeds_bound :
    ∃ tsk_k R_k,
      (tsk_k, R_k) ∈ hp_bounds ∧
      min (task_interference job_arrival job_cost job_task sched alpha j tsk_k
        (job_arrival j) (job_arrival j + R))
        (R - task_cost tsk + 1) >
      min (W task_cost task_period tsk_k R_k R)
        (R - task_cost tsk + 1) := by
  by_contra hAll
  push_neg at hAll
  have hSum := bertogna_fp_sum_exceeds_total_interference task_cost task_period task_deadline
    job_arrival job_cost job_deadline job_task arr_seq H_sporadic_tasks
    H_valid_job_parameters ts H_valid_task_parameters H_constrained_deadlines
    H_all_jobs_from_taskset H_ts_nodup (num_cpus := num_cpus) alpha sched
    H_jobs_come_from_arrival_sequence H_sequential_jobs H_jobs_must_arrive_to_execute
    H_completed_jobs_dont_execute higher_eq_priority H_respects_affinity
    H_work_conserving H_respects_FP_policy tsk task_in_ts alpha'
    H_affinity_subset H_at_least_one_cpu hp_bounds
    H_response_time_of_interfering_tasks_is_known H_hp_bounds_has_interfering_tasks
    H_response_time_bounds_ge_cost H_interfering_tasks_miss_no_deadlines R
    H_response_time_recurrence_holds H_response_time_no_larger_than_deadline
    j H_j_arrives H_job_of_tsk H_j_not_completed H_previous_jobs_of_tsk_completed
  set hp_filt := hp_bounds.filter (fun tsk_R =>
    decide (higher_priority_task_in alpha higher_eq_priority tsk (alpha' tsk) tsk_R.1))
  have hSumLe : ∀ (L : List (sporadic_task × Time)),
      (∀ p ∈ L, min (task_interference job_arrival job_cost job_task sched alpha j p.1
                      (job_arrival j) (job_arrival j + R)) (R - task_cost tsk + 1) ≤
                  min (W task_cost task_period p.1 p.2 R) (R - task_cost tsk + 1)) →
      (L.map (fun tsk_R => min (task_interference job_arrival job_cost job_task sched alpha j tsk_R.1
        (job_arrival j) (job_arrival j + R)) (R - task_cost tsk + 1))).sum ≤
      (L.map (fun tsk_R => min (W task_cost task_period tsk_R.1 tsk_R.2 R)
        (R - task_cost tsk + 1))).sum := by
    intro L hL
    induction L with
    | nil => simp
    | cons hd tl ih =>
      simp only [List.map_cons, List.sum_cons]
      exact Nat.add_le_add (hL hd (List.mem_cons_self))
        (ih fun p hMem => hL p (List.mem_cons_of_mem _ hMem))
  have hLe := hSumLe hp_filt (fun p hMem => by
    have hInBounds : p ∈ hp_bounds := List.mem_of_mem_filter hMem
    exact hAll p.1 p.2 hInBounds)
  have hEq :
      (hp_filt.map (fun tsk_R => min (W task_cost task_period tsk_R.1 tsk_R.2 R)
        (R - task_cost tsk + 1))).sum =
      total_interference_bound_fp task_cost task_period alpha tsk
        (alpha' tsk) hp_bounds R higher_eq_priority := by
    unfold total_interference_bound_fp interference_bound_generic
    rfl
  rw [hEq] at hLe
  exact absurd hSum (not_lt.mpr hLe)

end DerivingContradiction

end Lemmas

include H_sporadic_tasks H_valid_job_parameters H_valid_task_parameters
  H_constrained_deadlines H_all_jobs_from_taskset H_jobs_come_from_arrival_sequence
  H_sequential_jobs H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
  H_respects_affinity H_work_conserving H_respects_FP_policy
  task_in_ts H_affinity_subset H_at_least_one_cpu
  H_response_time_of_interfering_tasks_is_known H_hp_bounds_has_interfering_tasks
  H_response_time_bounds_ge_cost H_interfering_tasks_miss_no_deadlines
  H_response_time_recurrence_holds H_response_time_no_larger_than_deadline

include H_sporadic_tasks H_valid_job_parameters H_valid_task_parameters H_constrained_deadlines H_all_jobs_from_taskset H_jobs_come_from_arrival_sequence H_sequential_jobs H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_respects_affinity H_work_conserving H_respects_FP_policy H_affinity_subset H_at_least_one_cpu H_response_time_of_interfering_tasks_is_known H_hp_bounds_has_interfering_tasks H_response_time_bounds_ge_cost H_interfering_tasks_miss_no_deadlines H_response_time_recurrence_holds H_response_time_no_larger_than_deadline H_ts_nodup in
theorem bertogna_cirinei_response_time_bound_fp :
    is_response_time_bound_of_task job_arrival job_cost job_task arr_seq sched tsk R := by
  suffices H : ∀ n, ∀ (j : Job), arrives_in arr_seq j → job_task j = tsk →
      job_arrival j + R = n → completed job_cost sched j (job_arrival j + R) by
    intro j hARR hJOB; exact H _ j hARR hJOB rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro j hARR hJOB hEqN
    by_contra hNCOMP
    have hPREV : ∀ j0, arrives_in arr_seq j0 → job_task j0 = tsk →
        job_arrival j0 < job_arrival j →
        completed job_cost sched j0 (job_arrival j0 + R) := by
      intro j0 hARR0 hJOB0 hLT0
      refine IH (job_arrival j0 + R) ?_ j0 hARR0 hJOB0 rfl
      simp only [Time] at *; omega
    obtain ⟨tsk_k, R_k, hMem, hMinGT⟩ :=
      bertogna_fp_exists_task_that_exceeds_bound
        task_cost task_period task_deadline job_arrival job_cost job_deadline job_task
        arr_seq H_sporadic_tasks H_valid_job_parameters ts H_valid_task_parameters
        H_constrained_deadlines H_all_jobs_from_taskset H_ts_nodup
        (num_cpus := num_cpus) alpha sched H_jobs_come_from_arrival_sequence
        H_sequential_jobs H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
        higher_eq_priority H_respects_affinity H_work_conserving H_respects_FP_policy
        tsk task_in_ts alpha' H_affinity_subset H_at_least_one_cpu hp_bounds
        H_response_time_of_interfering_tasks_is_known H_hp_bounds_has_interfering_tasks
        H_response_time_bounds_ge_cost H_interfering_tasks_miss_no_deadlines R
        H_response_time_recurrence_holds H_response_time_no_larger_than_deadline
        j hARR hJOB hNCOMP hPREV
    have hWB :=
      bertogna_fp_workload_bounds_interference
        task_cost task_period task_deadline job_arrival job_cost job_deadline job_task
        arr_seq H_sporadic_tasks H_valid_job_parameters ts H_valid_task_parameters
        H_constrained_deadlines H_all_jobs_from_taskset
        (num_cpus := num_cpus) alpha sched H_jobs_come_from_arrival_sequence
        H_sequential_jobs H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
        higher_eq_priority H_respects_affinity H_work_conserving H_respects_FP_policy
        tsk task_in_ts alpha' H_affinity_subset H_at_least_one_cpu hp_bounds
        H_response_time_of_interfering_tasks_is_known H_hp_bounds_has_interfering_tasks
        H_response_time_bounds_ge_cost H_interfering_tasks_miss_no_deadlines R
        H_response_time_recurrence_holds H_response_time_no_larger_than_deadline
        j hARR hJOB hNCOMP hPREV tsk_k R_k hMem
    exact absurd hMinGT (not_lt.mpr (min_le_min_right _ hWB))

end ResponseTimeBound

end ResponseTimeAnalysisFP

end Prosa.Classic.Analysis.Apa.Bertogna_fp_theory
