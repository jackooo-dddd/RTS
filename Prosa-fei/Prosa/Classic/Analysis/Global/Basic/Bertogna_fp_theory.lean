-- Translated from: ../rt-proofs/classic/analysis/global/basic/bertogna_fp_theory.v
import Prosa.Classic.Util.All
import Prosa.Classic.Model.Arrival.Basic.Task
import Prosa.Classic.Model.Arrival.Basic.Job
import Prosa.Classic.Model.Arrival.Basic.Arrival_sequence
import Prosa.Classic.Model.Arrival.Basic.Task_arrival
import Prosa.Classic.Model.Priority
import Prosa.Classic.Model.Schedule.Global.Workload
import Prosa.Classic.Model.Schedule.Global.Schedulability
import Prosa.Classic.Model.Schedule.Global.Response_time
import Prosa.Classic.Model.Schedule.Global.Basic.Schedule
import Prosa.Classic.Model.Schedule.Global.Basic.Platform
import Prosa.Classic.Model.Schedule.Global.Basic.Interference
import Prosa.Classic.Model.Schedule.Global.Basic.Constrained_deadlines
import Prosa.Classic.Analysis.Global.Basic.Workload_bound
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

set_option autoImplicit false

namespace Prosa.Classic.Analysis.Global.Basic.Bertogna_fp_theory

open Classical
open Prosa.Classic.Model.Time
open Prosa.Classic.Model.Arrival.Basic.Arrival_sequence
open Prosa.Classic.Model.Arrival.Basic.Task.SporadicTask
open Prosa.Classic.Model.Arrival.Basic.Task.SporadicTaskset
open Prosa.Classic.Model.Arrival.Basic.Task_arrival
open Prosa.Classic.Model.Arrival.Basic.Job
open Prosa.Classic.Model.Priority
open Prosa.Classic.Model.Schedule.Global.Basic.Schedule.Schedule
open Prosa.Classic.Model.Schedule.Global.Basic.Schedule.ScheduleOfSporadicTask
open Prosa.Classic.Model.Schedule.Global.Basic.Platform.Platform
open Prosa.Classic.Model.Schedule.Global.Basic.Interference
open Prosa.Classic.Model.Schedule.Global.Basic.Constrained_deadlines.ConstrainedDeadlines
open Prosa.Classic.Model.Schedule.Global.Workload
open Prosa.Classic.Model.Schedule.Global.Schedulability.Schedulability
open Prosa.Classic.Model.Schedule.Global.Response_time.ResponseTime
open Prosa.Classic.Analysis.Global.Basic.Workload_bound.WorkloadBound
open Prosa.Util.Div_mod

namespace ResponseTimeAnalysisFP

section InterferenceBoundFP

variable {sporadic_task : Type _} [DecidableEq sporadic_task]
variable (task_cost : sporadic_task → Time)
variable (task_period : sporadic_task → Time)

variable (tsk : sporadic_task)

def interference_bound_generic (delta : Time) (tsk_R : sporadic_task × Time) : ℕ :=
  let tsk_other := tsk_R.1
  let R_other := tsk_R.2
  min (W task_cost task_period tsk_other R_other delta) (delta - task_cost tsk + 1)

def total_interference_bound_fp (hp_bounds : List (sporadic_task × Time)) (delta : Time) : ℕ :=
  (hp_bounds.map (fun tsk_R => interference_bound_generic task_cost task_period tsk delta tsk_R)).sum

end InterferenceBoundFP

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

variable (arr_seq : Prosa.Classic.Model.Arrival.Basic.Arrival_sequence.arrival_sequence Job)

variable (H_sporadic_tasks :
  sporadic_task_model task_period job_arrival job_task arr_seq)
variable (H_valid_job_parameters :
  ∀ j,
    Prosa.Classic.Model.Arrival.Basic.Arrival_sequence.arrives_in arr_seq j →
    valid_sporadic_job task_cost task_deadline job_cost job_deadline job_task j)

variable (ts : List sporadic_task)
variable (H_valid_task_parameters :
  valid_sporadic_taskset task_cost task_period task_deadline ts)
variable (H_constrained_deadlines :
  ∀ tsk, tsk ∈ ts → task_deadline tsk ≤ task_period tsk)

variable (H_all_jobs_from_taskset :
  ∀ j, Prosa.Classic.Model.Arrival.Basic.Arrival_sequence.arrives_in arr_seq j → job_task j ∈ ts)

variable {num_cpus : ℕ}
variable (sched : schedule Job num_cpus)
variable (H_jobs_come_from_arrival_sequence :
  jobs_come_from_arrival_sequence sched arr_seq)

variable (H_sequential_jobs : sequential_jobs sched)
variable (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
variable (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)

variable (H_at_least_one_cpu : num_cpus > 0)

variable (higher_eq_priority : FP_policy sporadic_task)

variable (H_work_conserving : work_conserving job_arrival job_cost arr_seq sched)
variable (H_respects_FP_policy :
  respects_FP_policy job_arrival job_cost job_task arr_seq sched higher_eq_priority)

noncomputable def no_deadline_is_missed_by_tsk (tsk : sporadic_task) : Prop :=
  task_misses_no_deadline job_arrival job_cost job_deadline job_task arr_seq sched tsk

def response_time_bounded_by (tsk : sporadic_task) (R : Time) : Prop :=
  is_response_time_bound_of_task job_arrival job_cost job_task arr_seq sched tsk R

variable (tsk : sporadic_task)
variable (task_in_ts : tsk ∈ ts)
-- Required by the Lean port of `platform_fp_cpus_busy_with_interfering_tasks`
-- (the Lean upstream lemma counts via `List.length filter`, which needs ts.Nodup
-- to bound by num_cpus; the Coq counterpart used `count` and derived nodup
-- internally from the schedule structure).
variable (H_ts_nodup : ts.Nodup)

variable (hp_bounds : List (sporadic_task × Time))
variable (H_response_time_of_interfering_tasks_is_known :
  ∀ hp_tsk R,
    (hp_tsk, R) ∈ hp_bounds →
    is_response_time_bound_of_task job_arrival job_cost job_task arr_seq sched hp_tsk R)

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
    (hp_tsk, R) ∈ hp_bounds → R ≤ task_deadline hp_tsk)

variable (R : Time)
variable (H_response_time_recurrence_holds :
  R = task_cost tsk +
    div_floor
      (total_interference_bound_fp task_cost task_period tsk hp_bounds R)
      num_cpus)

variable (H_response_time_no_larger_than_deadline :
  R ≤ task_deadline tsk)

section Lemmas

variable (j : Job)
variable (H_j_arrives : Prosa.Classic.Model.Arrival.Basic.Arrival_sequence.arrives_in arr_seq j)
variable (H_job_of_tsk : job_task j = tsk)

variable (H_j_not_completed : ¬ completed job_cost sched j (job_arrival j + R))
variable (H_previous_jobs_of_tsk_completed :
  ∀ j0,
    Prosa.Classic.Model.Arrival.Basic.Arrival_sequence.arrives_in arr_seq j0 →
    job_task j0 = tsk →
    job_arrival j0 < job_arrival j →
    completed job_cost sched j0 (job_arrival j0 + R))

section LemmasAboutHPTasks

variable (tsk_other : sporadic_task)
variable (R_other : Time)
variable (H_response_time_of_tsk_other : (tsk_other, R_other) ∈ hp_bounds)

include H_sporadic_tasks H_valid_job_parameters H_valid_task_parameters
  H_constrained_deadlines H_all_jobs_from_taskset H_jobs_come_from_arrival_sequence
  H_completed_jobs_dont_execute H_jobs_must_arrive_to_execute H_sequential_jobs
  H_response_time_of_interfering_tasks_is_known H_response_time_bounds_ge_cost
  H_interfering_tasks_miss_no_deadlines H_j_arrives H_job_of_tsk
  H_j_not_completed H_previous_jobs_of_tsk_completed H_response_time_of_tsk_other

include H_sporadic_tasks H_valid_job_parameters H_valid_task_parameters H_constrained_deadlines H_all_jobs_from_taskset H_jobs_come_from_arrival_sequence H_sequential_jobs H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_at_least_one_cpu H_work_conserving H_respects_FP_policy H_response_time_of_interfering_tasks_is_known H_hp_bounds_has_interfering_tasks H_response_time_bounds_ge_cost H_interfering_tasks_miss_no_deadlines H_response_time_no_larger_than_deadline H_j_arrives H_job_of_tsk H_j_not_completed H_previous_jobs_of_tsk_completed H_response_time_of_tsk_other in
theorem bertogna_fp_workload_bounds_interference :
    task_interference job_arrival job_cost job_task sched j tsk_other
      (job_arrival j) (job_arrival j + R) ≤
    W task_cost task_period tsk_other R_other R := by
  -- Step 1: bound task_interference by the workload of tsk_other.
  have hStep1 :
      task_interference job_arrival job_cost job_task sched j tsk_other
        (job_arrival j) (job_arrival j + R) ≤
      workload job_task sched tsk_other (job_arrival j) (job_arrival j + R) :=
    task_interference_le_workload job_arrival job_cost job_task sched j
      tsk_other (job_arrival j) (job_arrival j + R)
  -- Step 2: bound the workload by W. Two cases:
  --   (a) tsk_other ∈ ts: apply workload_bounded_by_W
  --   (b) tsk_other ∉ ts: workload = 0 since no scheduled job has task = tsk_other.
  by_cases hTOin : tsk_other ∈ ts
  · -- Apply workload_bounded_by_W. Need its hypotheses on tsk_other.
    have hValidOther : is_valid_sporadic_task task_cost task_period task_deadline tsk_other :=
      H_valid_task_parameters tsk_other hTOin
    have hConstrOther : task_deadline tsk_other ≤ task_period tsk_other :=
      H_constrained_deadlines tsk_other hTOin
    have hRgeCost : R_other ≥ task_cost tsk_other :=
      H_response_time_bounds_ge_cost tsk_other R_other H_response_time_of_tsk_other
    have hRleD : R_other ≤ task_deadline tsk_other :=
      H_interfering_tasks_miss_no_deadlines tsk_other R_other H_response_time_of_tsk_other
    -- Build the response_time_bound hypothesis in the form workload_bounded_by_W expects.
    have hRespBound : ∀ (j' : Job),
        arrives_in arr_seq j' → job_task j' = tsk_other →
        job_arrival j' + R_other < job_arrival j + R →
        completed job_cost sched j' (job_arrival j' + R_other) := by
      intro j' hARR' hJOB' _
      exact H_response_time_of_interfering_tasks_is_known tsk_other R_other
        H_response_time_of_tsk_other j' hARR' hJOB'
    have hWB :=
      Prosa.Classic.Analysis.Global.Basic.Workload_bound.WorkloadBound.workload_bounded_by_W
        task_cost task_period task_deadline job_arrival job_cost job_task job_deadline
        arr_seq H_valid_job_parameters
        (num_cpus := num_cpus) sched H_jobs_come_from_arrival_sequence
        H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_sequential_jobs
        H_sporadic_tasks tsk_other hValidOther hConstrOther
        (job_arrival j) R R_other hRespBound hRgeCost hRleD
    exact le_trans hStep1 hWB
  · -- tsk_other ∉ ts: workload = 0.
    have hWZero : workload job_task sched tsk_other (job_arrival j) (job_arrival j + R) = 0 := by
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
  H_completed_jobs_dont_execute H_jobs_must_arrive_to_execute H_sequential_jobs
  H_at_least_one_cpu H_work_conserving H_respects_FP_policy
  H_response_time_of_interfering_tasks_is_known H_hp_bounds_has_interfering_tasks
  H_response_time_bounds_ge_cost H_interfering_tasks_miss_no_deadlines
  H_response_time_no_larger_than_deadline
  H_j_arrives H_job_of_tsk H_j_not_completed H_previous_jobs_of_tsk_completed

include H_sporadic_tasks H_valid_job_parameters H_valid_task_parameters H_constrained_deadlines H_all_jobs_from_taskset H_jobs_come_from_arrival_sequence H_sequential_jobs H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_at_least_one_cpu H_work_conserving H_respects_FP_policy H_response_time_of_interfering_tasks_is_known H_hp_bounds_has_interfering_tasks H_response_time_bounds_ge_cost H_interfering_tasks_miss_no_deadlines H_response_time_recurrence_holds H_response_time_no_larger_than_deadline H_j_arrives H_job_of_tsk H_j_not_completed H_previous_jobs_of_tsk_completed in
/-- Coq `bertogna_fp_too_much_interference` (basic/bertogna_fp_theory.v): since
job `j` did not complete by `arr+R`, the total interference `X ≥ R - cost + 1`. -/
theorem bertogna_fp_too_much_interference :
    total_interference job_arrival job_cost sched j
      (job_arrival j) (job_arrival j + R) ≥
    R - task_cost tsk + 1 := by
  -- Strategy: for each slot t ∈ [arr j, arr j + R), backlogged_indicator(t) +
  -- service_at(t) ≥ 1, because if not backlogged then either j is scheduled
  -- (service_at ≥ 1) or j is already completed at t — but completion_monotonic
  -- would then force completion at arr+R, contradicting H_j_not_completed.
  -- Summing: R ≤ X + service(arr j, arr j + R). Then service(arr,arr+R) is
  -- bounded by `job_cost j - 1` (NOTCOMP) and `job_cost j ≤ task_cost tsk`.
  set X := total_interference job_arrival job_cost sched j
              (job_arrival j) (job_arrival j + R) with hXdef
  -- Bound: cost j ≤ task_cost tsk
  have hCostLe : job_cost j ≤ task_cost tsk := by
    have hVJP := H_valid_job_parameters j H_j_arrives
    have hcost := hVJP.2.1
    unfold job_cost_le_task_cost at hcost
    rw [H_job_of_tsk] at hcost
    exact hcost
  -- Service at arr+R is < job_cost j (since j not completed there)
  have hServLt : service sched j (job_arrival j + R) < job_cost j := by
    by_contra hge
    push_neg at hge
    exact H_j_not_completed hge
  -- Per-slot inequality: 1 ≤ backlogged_indicator + service_at,
  -- for any t in [arr j, arr j + R)
  have hSlot : ∀ t ∈ Finset.Ico (job_arrival j) (job_arrival j + R),
      (1 : ℕ) ≤ (if backlogged job_arrival job_cost sched j t then 1 else 0) +
                  service_at sched j t := by
    intro t ht
    rw [Finset.mem_Ico] at ht
    by_cases hback : backlogged job_arrival job_cost sched j t
    · simp [hback]
    -- not backlogged: either not pending or scheduled
    · simp only [hback, if_false, zero_add]
      unfold backlogged at hback
      push_neg at hback
      -- We need to use classical reasoning to extract: ¬(pending ∧ ¬scheduled)
      by_cases hSched : scheduled sched j t
      · -- Scheduled, so service_at ≥ 1
        rcases hSched with ⟨cpu, hOn⟩
        unfold service_at
        calc (1 : ℕ)
            = (if scheduled_on sched j cpu t = true then 1 else 0) := by simp [hOn]
          _ ≤ ∑ cpu' : Fin num_cpus,
                (if scheduled_on sched j cpu' t = true then 1 else 0) :=
              Finset.single_le_sum
                (f := fun c => if scheduled_on sched j c t = true then 1 else 0)
                (fun _ _ => Nat.zero_le _)
                (Finset.mem_univ cpu)
      · -- Not scheduled and not backlogged: hence not pending, hence completed
        have hNotPending : ¬ pending job_arrival job_cost sched j t := by
          intro hP
          exact hSched (hback hP)
        unfold pending at hNotPending
        push_neg at hNotPending
        -- has_arrived since t ≥ arr j
        have hArr : has_arrived job_arrival j t := ht.1
        have hCompT : completed job_cost sched j t := hNotPending hArr
        -- monotonic to arr+R
        have hCompR : completed job_cost sched j (job_arrival j + R) :=
          completion_monotonic job_cost sched j H_completed_jobs_dont_execute
            t (job_arrival j + R) (le_of_lt ht.2) hCompT
        exact absurd hCompR H_j_not_completed
  -- Sum up the per-slot bound
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
    -- LHS of h1: R ≤ X + service_during(arr, arr+R)
    have hXunfold :
        ∑ t ∈ Finset.Ico (job_arrival j) (job_arrival j + R),
          (if backlogged job_arrival job_cost sched j t then 1 else 0) = X := by
      rw [hXdef]; rfl
    rw [hXunfold] at h1
    exact h1
  -- service_during(arr, arr+R) = service(arr+R) (using
  -- service_before_arrival_eq_service_during with t0 = 0)
  have hServEq :
      ∑ t ∈ Finset.Ico (job_arrival j) (job_arrival j + R), service_at sched j t =
      service sched j (job_arrival j + R) := by
    unfold service
    have := service_before_arrival_eq_service_during
              job_arrival sched j H_jobs_must_arrive_to_execute
              0 R (Nat.zero_le _)
    exact this.symm
  rw [hServEq] at hSum
  -- The recurrence implies task_cost tsk ≤ R.
  have hCostLeR : task_cost tsk ≤ R := by
    rw [H_response_time_recurrence_holds]; exact Nat.le_add_right _ _
  -- Manually derive R - task_cost tsk + 1 ≤ X using Nat lemmas
  -- (avoiding omega so opaque function applications stay opaque).
  -- Step 1: R + 1 ≤ X + task_cost tsk
  have hStep : R + 1 ≤ X + task_cost tsk :=
    calc R + 1
        ≤ (X + service sched j (job_arrival j + R)) + 1 :=
          Nat.add_le_add_right hSum 1
      _ = X + (service sched j (job_arrival j + R) + 1) := (Nat.add_assoc _ _ _)
      _ ≤ X + job_cost j := Nat.add_le_add_left hServLt X
      _ ≤ X + task_cost tsk := Nat.add_le_add_left hCostLe X
  -- Step 2: R + 1 ≤ X + task_cost tsk and task_cost tsk ≤ R imply
  -- R - task_cost tsk + 1 ≤ X.
  -- Use Nat.sub_add_cancel: task_cost ≤ R → R - task_cost + task_cost = R.
  have hCancel : (R - task_cost tsk) + task_cost tsk = R :=
    Nat.sub_add_cancel hCostLeR
  -- Plug in: ((R - task_cost) + task_cost) + 1 ≤ X + task_cost
  --       → (R - task_cost + 1) + task_cost ≤ X + task_cost
  --       → R - task_cost + 1 ≤ X.
  have hStep' : (R - task_cost tsk + 1) + task_cost tsk ≤ X + task_cost tsk := by
    have : (R - task_cost tsk + 1) + task_cost tsk = R + 1 := by
      rw [Nat.add_right_comm]; rw [hCancel]
    rw [this]; exact hStep
  exact Nat.le_of_add_le_add_right hStep'

include H_sporadic_tasks H_valid_job_parameters H_valid_task_parameters H_constrained_deadlines H_all_jobs_from_taskset H_jobs_come_from_arrival_sequence H_sequential_jobs H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_at_least_one_cpu H_work_conserving H_respects_FP_policy task_in_ts H_response_time_of_interfering_tasks_is_known H_hp_bounds_has_interfering_tasks H_response_time_bounds_ge_cost H_interfering_tasks_miss_no_deadlines H_response_time_no_larger_than_deadline H_j_arrives H_job_of_tsk H_j_not_completed H_previous_jobs_of_tsk_completed in
theorem bertogna_fp_interference_by_different_tasks :
    ∀ t j_other,
      job_arrival j ≤ t ∧ t < job_arrival j + R →
      Prosa.Classic.Model.Arrival.Basic.Arrival_sequence.arrives_in arr_seq j_other →
      backlogged job_arrival job_cost sched j t →
      scheduled sched j_other t →
      job_task j_other ≠ tsk := by
  -- Coq strategy: case-split on `arr j_other < arr j`. Either the previous
  -- job of `tsk` (= j_other) was already completed, contradicting `pending`;
  -- or sporadic arrivals push arr j_other past arr j + R, contradicting
  -- `j_other` being pending at t < arr j + R.
  intro t j_other ht hARRother hBACK hSCHED hSAMEtsk
  have hPEND : pending job_arrival job_cost sched j_other t :=
    scheduled_implies_pending job_arrival job_cost sched j_other
      H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute t hSCHED
  have hRleD : R ≤ task_deadline tsk := H_response_time_no_larger_than_deadline
  have hDleP : task_deadline tsk ≤ task_period tsk :=
    H_constrained_deadlines tsk task_in_ts
  rcases lt_or_ge (job_arrival j_other) (job_arrival j) with hLT | hGE
  · -- Case 1: arr j_other < arr j; PREV says j_other completed at arr+R.
    have hNeq : j_other ≠ j := by
      intro h; subst h; exact Nat.lt_irrefl _ hLT
    have hPrev := H_previous_jobs_of_tsk_completed j_other hARRother hSAMEtsk hLT
    have hSpo :=
      H_sporadic_tasks j_other j hNeq hARRother H_j_arrives
        (by rw [hSAMEtsk, H_job_of_tsk]) (le_of_lt hLT)
    rw [hSAMEtsk] at hSpo
    have hLE : job_arrival j_other + R ≤ t := by
      have h1 : job_arrival j ≤ t := ht.1
      simp only [Time] at *; omega
    have hCompT : completed job_cost sched j_other t :=
      completion_monotonic job_cost sched j_other H_completed_jobs_dont_execute
        _ _ hLE hPrev
    exact hPEND.2 hCompT
  · -- Case 2: arr j_other ≥ arr j.
    by_cases hEq : j_other = j
    · -- Same job: scheduled at t contradicts backlogged.
      subst hEq; exact hBACK.2 hSCHED
    · -- Different job, same task: sporadic forces arr j_other ≥ arr j + period.
      have hSpo :=
        H_sporadic_tasks j j_other (Ne.symm hEq) H_j_arrives hARRother
          (by rw [H_job_of_tsk, hSAMEtsk]) hGE
      rw [H_job_of_tsk] at hSpo
      have hArrJotherT : job_arrival j_other ≤ t := hPEND.1
      have hLT_t : t < job_arrival j_other := by
        have h2 : t < job_arrival j + R := ht.2
        simp only [Time] at *; omega
      exact absurd hArrJotherT (not_le.mpr hLT_t)

include H_sporadic_tasks H_valid_job_parameters H_valid_task_parameters H_constrained_deadlines H_all_jobs_from_taskset H_jobs_come_from_arrival_sequence H_sequential_jobs H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_at_least_one_cpu H_work_conserving H_respects_FP_policy task_in_ts H_ts_nodup H_response_time_of_interfering_tasks_is_known H_hp_bounds_has_interfering_tasks H_response_time_bounds_ge_cost H_interfering_tasks_miss_no_deadlines H_response_time_no_larger_than_deadline H_j_arrives H_job_of_tsk H_j_not_completed H_previous_jobs_of_tsk_completed in
theorem bertogna_fp_all_cpus_are_busy :
    ∀ t,
      job_arrival j ≤ t ∧ t < job_arrival j + R →
      backlogged job_arrival job_cost sched j t →
      (ts.filter (fun tsk_other =>
        decide (task_is_scheduled job_task sched tsk_other t) &&
        higher_priority_task higher_eq_priority tsk tsk_other)).length = num_cpus := by
  -- Apply upstream `platform_fp_cpus_busy_with_interfering_tasks`. Need to
  -- bridge: (a) t < arr + period (from t < arr+R, R ≤ deadline ≤ period),
  -- (b) per-task completion at arr+task_period (via response-time hypothesis
  -- + completion_monotonic), (c) tsk's previous jobs completion at arr+period
  -- (similar bridge from H_previous_jobs_of_tsk_completed at arr+R).
  intro t ht hBACK
  have hValidTask := H_valid_task_parameters tsk task_in_ts
  have hRleD : R ≤ task_deadline tsk := H_response_time_no_larger_than_deadline
  have hDleP : task_deadline tsk ≤ task_period tsk :=
    H_constrained_deadlines tsk task_in_ts
  have hT_before_period : t < job_arrival j + task_period tsk := by
    have h2 := ht.2; simp only [Time] at *; omega
  have hPrevHP : ∀ j_other tsk_other,
      arrives_in arr_seq j_other →
      job_task j_other = tsk_other →
      higher_priority_task higher_eq_priority tsk tsk_other = true →
      completed job_cost sched j_other
        (job_arrival j_other + task_period tsk_other) := by
    intro j_other tsk_other hARR hJOB hINTERF
    have hOtherInTs : tsk_other ∈ ts := hJOB ▸ H_all_jobs_from_taskset j_other hARR
    obtain ⟨R', hRin⟩ := H_hp_bounds_has_interfering_tasks tsk_other hOtherInTs hINTERF
    have hCompR' : completed job_cost sched j_other (job_arrival j_other + R') :=
      H_response_time_of_interfering_tasks_is_known tsk_other R' hRin j_other hARR hJOB
    have hR'leD : R' ≤ task_deadline tsk_other :=
      H_interfering_tasks_miss_no_deadlines tsk_other R' hRin
    have hD_otherLeP : task_deadline tsk_other ≤ task_period tsk_other :=
      H_constrained_deadlines tsk_other hOtherInTs
    have hLE : job_arrival j_other + R' ≤ job_arrival j_other + task_period tsk_other := by
      simp only [Time] at *; omega
    exact completion_monotonic job_cost sched j_other
      H_completed_jobs_dont_execute _ _ hLE hCompR'
  have hPrevTsk : ∀ j0,
      arrives_in arr_seq j0 → job_task j0 = tsk →
      job_arrival j0 < job_arrival j →
      completed job_cost sched j0 (job_arrival j0 + task_period tsk) := by
    intro j0 hARR0 hJOB0 hLT0
    have hCompR : completed job_cost sched j0 (job_arrival j0 + R) :=
      H_previous_jobs_of_tsk_completed j0 hARR0 hJOB0 hLT0
    have hLE : job_arrival j0 + R ≤ job_arrival j0 + task_period tsk := by
      simp only [Time] at *; omega
    exact completion_monotonic job_cost sched j0
      H_completed_jobs_dont_execute _ _ hLE hCompR
  have hUp :=
    Prosa.Classic.Model.Schedule.Global.Basic.Constrained_deadlines.ConstrainedDeadlines.platform_fp_cpus_busy_with_interfering_tasks
      task_cost task_period task_deadline job_arrival job_cost job_deadline job_task
      arr_seq sched H_jobs_come_from_arrival_sequence H_valid_job_parameters
      higher_eq_priority H_work_conserving H_respects_FP_policy
      ts H_ts_nodup H_all_jobs_from_taskset H_sequential_jobs H_completed_jobs_dont_execute
      H_jobs_must_arrive_to_execute H_sporadic_tasks tsk hValidTask
      j H_j_arrives H_job_of_tsk t hBACK hT_before_period
      hPrevHP hPrevTsk
  -- Bridge predicate forms: `decide (task_is_scheduled ...) =
  -- decide (∃ cpu, task_scheduled_on ...)`. The two `decide`s use
  -- different `Decidable` instances (Classical.propDecidable vs
  -- Nat.decidableExistsFin); use `Bool` extensionality to reconcile.
  unfold Prosa.Classic.Model.Schedule.Global.Basic.Constrained_deadlines.ConstrainedDeadlines.scheduled_task_with_higher_eq_priority at hUp
  rw [show (fun tsk_other =>
        decide (task_is_scheduled job_task sched tsk_other t) &&
        higher_priority_task higher_eq_priority tsk tsk_other) =
      (fun tsk_other =>
        @decide (∃ cpu : Fin num_cpus, task_scheduled_on job_task sched tsk_other cpu t = true)
                (Nat.decidableExistsFin _) &&
        higher_priority_task higher_eq_priority tsk tsk_other) from ?_]
  · exact hUp
  · funext tsk_other
    have : decide (task_is_scheduled job_task sched tsk_other t) =
        @decide (∃ cpu : Fin num_cpus, task_scheduled_on job_task sched tsk_other cpu t = true)
                (Nat.decidableExistsFin _) := by
      unfold task_is_scheduled
      by_cases h : ∃ cpu : Fin num_cpus, task_scheduled_on job_task sched tsk_other cpu t = true
      · simp [h]
      · simp [h]
    rw [this]

include H_sporadic_tasks H_valid_job_parameters H_valid_task_parameters H_constrained_deadlines H_all_jobs_from_taskset H_jobs_come_from_arrival_sequence H_sequential_jobs H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_at_least_one_cpu H_work_conserving H_respects_FP_policy task_in_ts H_ts_nodup H_response_time_of_interfering_tasks_is_known H_hp_bounds_has_interfering_tasks H_response_time_bounds_ge_cost H_interfering_tasks_miss_no_deadlines H_response_time_no_larger_than_deadline H_j_arrives H_job_of_tsk H_j_not_completed H_previous_jobs_of_tsk_completed in
theorem bertogna_fp_interference_on_all_cpus :
    ((ts.filter (fun tsk_other =>
        higher_priority_task higher_eq_priority tsk tsk_other)).map
      (fun tsk_k => task_interference job_arrival job_cost job_task sched j tsk_k
        (job_arrival j) (job_arrival j + R))).sum =
    total_interference job_arrival job_cost sched j
      (job_arrival j) (job_arrival j + R) * num_cpus := by
  -- Coq strategy: exchange sums (task ↔ time), distribute backlogged indicator,
  -- and per-time use work_conserving + FP + DIFFTASK to show the inner sum
  -- = num_cpus when backlogged.
  set hp_tasks := ts.filter (fun tsk_other =>
    higher_priority_task higher_eq_priority tsk tsk_other) with hp_def
  -- Helper: swap (List.map (Finset.sum)).sum with Finset.sum (List.map _).sum.
  have hSwap1 : ∀ (L : List sporadic_task) (S : Finset ℕ) (f : sporadic_task → ℕ → ℕ),
      (L.map (fun x => ∑ i ∈ S, f x i)).sum = ∑ i ∈ S, (L.map (fun x => f x i)).sum := by
    intro L S f
    induction L with
    | nil => simp
    | cons a t ih => simp [ih, Finset.sum_add_distrib]
  have hSwap2 : ∀ (L : List sporadic_task) (f : sporadic_task → Fin num_cpus → ℕ),
      (L.map (fun x => ∑ i : Fin num_cpus, f x i)).sum =
        ∑ i : Fin num_cpus, (L.map (fun x => f x i)).sum := by
    intro L f
    induction L with
    | nil => simp
    | cons a t ih => simp [ih, Finset.sum_add_distrib]
  -- Unfold task_interference inside the map.
  show (((hp_tasks.map (fun tsk_k =>
      ∑ t ∈ Finset.Ico (job_arrival j) (job_arrival j + R),
        ∑ cpu : Fin num_cpus,
          if backlogged job_arrival job_cost sched j t ∧
             task_scheduled_on job_task sched tsk_k cpu t = true then 1 else 0)).sum) =
    ((∑ t ∈ Finset.Ico (job_arrival j) (job_arrival j + R),
      if backlogged job_arrival job_cost sched j t then 1 else 0) * num_cpus))
  -- Step 1: swap the outer Finset.sum_t with the list-sum.
  rw [hSwap1 hp_tasks (Finset.Ico (job_arrival j) (job_arrival j + R))
        (fun tsk_k t => ∑ cpu : Fin num_cpus,
          if backlogged job_arrival job_cost sched j t ∧
             task_scheduled_on job_task sched tsk_k cpu t = true then 1 else 0)]
  -- Step 2: also swap inner sum_cpu out (cpu and tsk_k swap), inside each t.
  simp_rw [hSwap2 hp_tasks]
  -- RHS: distribute multiplication.
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro t ht
  rw [Finset.mem_Ico] at ht
  -- For each t, show the per-time equality.
  by_cases hBack : backlogged job_arrival job_cost sched j t
  · -- Case backlogged: each cpu contributes exactly 1.
    rw [if_pos hBack, one_mul]
    -- For each cpu, the list-sum equals 1 (job_task of the busy job is in hp_tasks, all others contribute 0).
    have hPerCpu : ∀ cpu : Fin num_cpus,
        (hp_tasks.map (fun tsk_k => if backlogged job_arrival job_cost sched j t ∧
            task_scheduled_on job_task sched tsk_k cpu t = true then 1 else 0)).sum = 1 := by
      intro cpu
      obtain ⟨j_other, hOn⟩ := H_work_conserving j t H_j_arrives hBack cpu
      have hSchedOther : scheduled sched j_other t := ⟨cpu, hOn⟩
      have hARRother : arrives_in arr_seq j_other :=
        H_jobs_come_from_arrival_sequence j_other t hSchedOther
      have hFP : higher_eq_priority (job_task j_other) (job_task j) = true :=
        H_respects_FP_policy j j_other t H_j_arrives hBack hSchedOther
      have hDIFF : job_task j_other ≠ tsk :=
        bertogna_fp_interference_by_different_tasks task_cost task_period task_deadline
          job_arrival job_cost job_deadline job_task arr_seq H_sporadic_tasks
          H_valid_job_parameters ts H_valid_task_parameters
          H_constrained_deadlines H_all_jobs_from_taskset
          (num_cpus := num_cpus) sched H_jobs_come_from_arrival_sequence
          H_sequential_jobs H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
          H_at_least_one_cpu higher_eq_priority H_work_conserving H_respects_FP_policy
          tsk task_in_ts hp_bounds H_response_time_of_interfering_tasks_is_known
          H_hp_bounds_has_interfering_tasks H_response_time_bounds_ge_cost
          H_interfering_tasks_miss_no_deadlines R
          H_response_time_no_larger_than_deadline j H_j_arrives H_job_of_tsk
          H_j_not_completed H_previous_jobs_of_tsk_completed
          t j_other ⟨ht.1, ht.2⟩ hARRother hBack hSchedOther
      have hOtherInTs : job_task j_other ∈ ts :=
        H_all_jobs_from_taskset j_other hARRother
      have hOtherInHp : job_task j_other ∈ hp_tasks := by
        rw [hp_def, List.mem_filter]
        refine ⟨hOtherInTs, ?_⟩
        unfold higher_priority_task
        rw [H_job_of_tsk] at hFP
        simp [hFP, decide_eq_true_eq, hDIFF]
      have hTSOn : task_scheduled_on job_task sched (job_task j_other) cpu t = true := by
        unfold task_scheduled_on
        unfold scheduled_on at hOn
        cases h_sc : sched cpu t with
        | none => rw [h_sc] at hOn; simp at hOn
        | some j' => rw [h_sc] at hOn; simp at hOn; subst hOn; simp
      -- For all other tsk_k ≠ job_task j_other, the indicator is 0
      have hOtherZero : ∀ tsk_k, tsk_k ≠ job_task j_other →
          (if backlogged job_arrival job_cost sched j t ∧
              task_scheduled_on job_task sched tsk_k cpu t = true then (1:ℕ) else 0) = 0 := by
        intro tsk_k hNeq
        have hTaskFalse : task_scheduled_on job_task sched tsk_k cpu t = false := by
          unfold task_scheduled_on
          cases h_sc : sched cpu t with
          | none => rfl
          | some j' =>
            simp only
            have hjj : j' = j_other := by
              unfold scheduled_on at hOn
              rw [h_sc] at hOn; simp at hOn; exact hOn
            subst hjj
            simp [hNeq.symm]
        simp [hTaskFalse]
      -- hp_tasks is Nodup (filter of ts which is Nodup)
      have hHpNodup : hp_tasks.Nodup := List.Nodup.filter _ H_ts_nodup
      -- Convert list sum to finset sum and use sum_eq_single
      rw [← List.sum_toFinset _ hHpNodup]
      rw [Finset.sum_eq_single (job_task j_other)]
      · simp [hBack, hTSOn]
      · intro tsk_k hMem hNeq
        have : tsk_k ≠ job_task j_other := hNeq
        exact hOtherZero tsk_k this
      · intro hNotMem
        exfalso
        apply hNotMem
        rw [List.mem_toFinset]
        exact hOtherInHp
    -- Sum over cpu of 1 = num_cpus
    rw [show (∑ cpu : Fin num_cpus,
        (hp_tasks.map (fun tsk_k => if backlogged job_arrival job_cost sched j t ∧
            task_scheduled_on job_task sched tsk_k cpu t = true then (1:ℕ) else 0)).sum) =
        ∑ _cpu : Fin num_cpus, 1 from Finset.sum_congr rfl (fun cpu _ => hPerCpu cpu)]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
  · -- Not backlogged: indicator and the inner sum are 0.
    rw [if_neg hBack, zero_mul]
    apply Finset.sum_eq_zero
    intro cpu _
    apply List.sum_eq_zero
    intro x hx
    obtain ⟨tsk_k, _, h_eq⟩ := List.mem_map.mp hx
    rw [← h_eq]
    rw [if_neg]
    intro ⟨h1, _⟩
    exact hBack h1

include H_sporadic_tasks H_valid_job_parameters H_valid_task_parameters H_constrained_deadlines H_all_jobs_from_taskset H_jobs_come_from_arrival_sequence H_sequential_jobs H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_at_least_one_cpu H_work_conserving H_respects_FP_policy task_in_ts H_ts_nodup H_response_time_of_interfering_tasks_is_known H_hp_bounds_has_interfering_tasks H_response_time_bounds_ge_cost H_interfering_tasks_miss_no_deadlines H_response_time_no_larger_than_deadline H_j_arrives H_job_of_tsk H_j_not_completed H_previous_jobs_of_tsk_completed in
set_option maxHeartbeats 800000 in
theorem bertogna_fp_interference_in_non_full_processors :
    let hp := ts.filter (fun tsk_other =>
      higher_priority_task higher_eq_priority tsk tsk_other)
    let x_val := fun (i : sporadic_task) =>
      task_interference job_arrival job_cost job_task sched j i
        (job_arrival j) (job_arrival j + R)
    ∀ (delta : ℕ),
      let num_exceeding := (hp.filter (fun i => decide (x_val i ≥ delta))).length
      0 < num_exceeding ∧ num_exceeding < num_cpus →
      ((hp.filter (fun i => decide (x_val i < delta))).map (fun i => x_val i)).sum ≥
      delta * (num_cpus - num_exceeding) := by
  intro hp x_val delta num_exceeding ⟨hHAS, hLT⟩
  set hpE := hp.filter (fun i => decide (x_val i ≥ delta)) with hpE_def
  set hpL := hp.filter (fun i => decide (x_val i < delta)) with hpL_def
  set k := hpE.length with k_def
  change k = num_exceeding at k_def
  rw [← k_def] at hHAS hLT

  -- Use bertogna_fp_interference_on_all_cpus: Σ_{hp} x_val(k) = TI * m
  have hINV := bertogna_fp_interference_on_all_cpus task_cost task_period task_deadline
    job_arrival job_cost job_deadline job_task arr_seq H_sporadic_tasks
    H_valid_job_parameters ts H_valid_task_parameters H_constrained_deadlines
    H_all_jobs_from_taskset (num_cpus := num_cpus) sched
    H_jobs_come_from_arrival_sequence H_sequential_jobs H_jobs_must_arrive_to_execute
    H_completed_jobs_dont_execute H_at_least_one_cpu higher_eq_priority
    H_work_conserving H_respects_FP_policy tsk task_in_ts H_ts_nodup hp_bounds
    H_response_time_of_interfering_tasks_is_known H_hp_bounds_has_interfering_tasks
    H_response_time_bounds_ge_cost H_interfering_tasks_miss_no_deadlines R
    H_response_time_no_larger_than_deadline
    j H_j_arrives H_job_of_tsk H_j_not_completed H_previous_jobs_of_tsk_completed

  set TI := total_interference job_arrival job_cost sched j
    (job_arrival j) (job_arrival j + R) with TI_def

  -- ── hOneJobPerTask: each hp task is on at most 1 CPU per time slot ──
  -- Build the completion hypotheses needed by the platform lemma
  -- (same pattern as bertogna_fp_all_cpus_are_busy).
  have hValidTask := H_valid_task_parameters tsk task_in_ts
  have hRleD : R ≤ task_deadline tsk := H_response_time_no_larger_than_deadline
  have hDleP : task_deadline tsk ≤ task_period tsk :=
    H_constrained_deadlines tsk task_in_ts
  have hPrevHP_period : ∀ j0 tsk0,
      arrives_in arr_seq j0 → job_task j0 = tsk0 →
      higher_priority_task higher_eq_priority tsk tsk0 = true →
      completed job_cost sched j0 (job_arrival j0 + task_period tsk0) := by
    intro j0 tsk0 hA0 hJ0 hInt0
    have hIn0 : tsk0 ∈ ts := hJ0 ▸ H_all_jobs_from_taskset j0 hA0
    obtain ⟨R0, hR0⟩ := H_hp_bounds_has_interfering_tasks tsk0 hIn0 hInt0
    have hComp := H_response_time_of_interfering_tasks_is_known tsk0 R0 hR0 j0 hA0 hJ0
    exact completion_monotonic job_cost sched j0 H_completed_jobs_dont_execute _ _ (by
      have := H_interfering_tasks_miss_no_deadlines tsk0 R0 hR0
      have := H_constrained_deadlines tsk0 hIn0; simp only [Time] at *; omega) hComp
  have hPrevTsk : ∀ j0,
      arrives_in arr_seq j0 → job_task j0 = tsk →
      job_arrival j0 < job_arrival j →
      completed job_cost sched j0 (job_arrival j0 + task_period tsk) := by
    intro j0 hA0 hJ0 hLt0
    exact completion_monotonic job_cost sched j0 H_completed_jobs_dont_execute _ _ (by
      simp only [Time] at *; omega) (H_previous_jobs_of_tsk_completed j0 hA0 hJ0 hLt0)

  -- hOneJobPerTask: at each backlogged t in the window, if two jobs of the same
  -- task are scheduled on cpu1 and cpu2, then cpu1 = cpu2.
  have hOneJobPerTask : ∀ t,
      job_arrival j ≤ t ∧ t < job_arrival j + R →
      backlogged job_arrival job_cost sched j t →
      ∀ cpu1 cpu2 : Fin num_cpus, ∀ j1 j2 : Job,
        sched cpu1 t = some j1 → sched cpu2 t = some j2 →
        job_task j1 = job_task j2 →
        cpu1 = cpu2 := by
    intro t ht hbl cpu1 cpu2 j1 j2 h1 h2 hsame
    have hSched1 : scheduled sched j1 t := ⟨cpu1, by unfold scheduled_on; rw [h1]; simp⟩
    have hSched2 : scheduled sched j2 t := ⟨cpu2, by unfold scheduled_on; rw [h2]; simp⟩
    have hPend1 : pending job_arrival job_cost sched j1 t :=
      scheduled_implies_pending job_arrival job_cost sched j1
        H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute t hSched1
    have hPend2 : pending job_arrival job_cost sched j2 t :=
      scheduled_implies_pending job_arrival job_cost sched j2
        H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute t hSched2
    have hArr1 := H_jobs_come_from_arrival_sequence j1 t hSched1
    have hArr2 := H_jobs_come_from_arrival_sequence j2 t hSched2
    have hT_lt_per : t < job_arrival j + task_period tsk := by
      simp only [Time] at *; omega
    -- Case split: is job_task j1 = tsk?
    by_cases hSameTsk : job_task j1 = tsk
    · -- j1's task = tsk → contradiction with backlogged
      exfalso
      exact (bertogna_fp_interference_by_different_tasks task_cost task_period task_deadline
        job_arrival job_cost job_deadline job_task arr_seq H_sporadic_tasks
        H_valid_job_parameters ts H_valid_task_parameters H_constrained_deadlines
        H_all_jobs_from_taskset (num_cpus := num_cpus) sched
        H_jobs_come_from_arrival_sequence H_sequential_jobs H_jobs_must_arrive_to_execute
        H_completed_jobs_dont_execute H_at_least_one_cpu higher_eq_priority
        H_work_conserving H_respects_FP_policy tsk task_in_ts hp_bounds
        H_response_time_of_interfering_tasks_is_known H_hp_bounds_has_interfering_tasks
        H_response_time_bounds_ge_cost H_interfering_tasks_miss_no_deadlines R
        H_response_time_no_larger_than_deadline
        j H_j_arrives H_job_of_tsk H_j_not_completed H_previous_jobs_of_tsk_completed
        t j1 ht hArr1 hbl hSched1) hSameTsk
    · -- j1's task ≠ tsk: use platform uniqueness
      have hFP1 : higher_eq_priority (job_task j1) (job_task j) = true :=
        H_respects_FP_policy j j1 t H_j_arrives hbl hSched1
      have hHP1 : higher_priority_task higher_eq_priority tsk (job_task j1) = true := by
        unfold higher_priority_task
        rw [H_job_of_tsk] at hFP1; simp [hFP1, hSameTsk]
      have hEqJob : j1 = j2 :=
        Prosa.Classic.Model.Schedule.Global.Basic.Constrained_deadlines.ConstrainedDeadlines.platform_fp_no_multiple_jobs_of_interfering_tasks
          task_cost task_period task_deadline job_arrival job_cost job_deadline job_task
          arr_seq sched H_jobs_come_from_arrival_sequence H_valid_job_parameters
          higher_eq_priority H_work_conserving H_respects_FP_policy
          ts H_all_jobs_from_taskset H_sequential_jobs
          H_completed_jobs_dont_execute H_jobs_must_arrive_to_execute H_sporadic_tasks
          tsk hValidTask j H_j_arrives H_job_of_tsk t hbl hT_lt_per
          hPrevHP_period hPrevTsk
          j1 j2 hArr1 hArr2 hPend1 hPend2 hsame hHP1
      cases hEqJob
      exact H_sequential_jobs j1 t cpu1 cpu2 h1 h2

  -- ── hSingleLeTotal: ∀ i ∈ hp, x_val(i) ≤ TI ──
  have hSingleLeTotal : ∀ i ∈ hp, x_val i ≤ TI := by
    intro i _hi
    simp only [TI_def, task_interference, total_interference]
    apply Finset.sum_le_sum
    intro t _ht
    by_cases hbl : backlogged job_arrival job_cost sched j t
    · simp only [hbl, ite_true, true_and]
      by_cases hSched : ∃ cpu : Fin num_cpus, task_scheduled_on job_task sched i cpu t = true
      · obtain ⟨cpu0, hcpu0⟩ := hSched
        have hAtMost1 : ∀ cpu : Fin num_cpus,
            (if task_scheduled_on job_task sched i cpu t = true then (1:ℕ) else 0) =
            if cpu = cpu0 then 1 else 0 := by
          intro cpu
          by_cases heq : cpu = cpu0
          · subst heq; simp [hcpu0]
          · have hFalse : task_scheduled_on job_task sched i cpu t = false := by
              cases htso : task_scheduled_on job_task sched i cpu t with
              | false => rfl
              | true =>
                exfalso
                unfold task_scheduled_on at htso hcpu0
                cases h1 : sched cpu t with
                | none => simp [h1] at htso
                | some jc =>
                  cases h2 : sched cpu0 t with
                  | none => simp [h2] at hcpu0
                  | some jc0 =>
                    simp [h1] at htso; simp [h2] at hcpu0
                    have hSameTask : job_task jc = job_task jc0 := by rw [htso, hcpu0]
                    have ht_range : job_arrival j ≤ t ∧ t < job_arrival j + R := by
                      rwa [Finset.mem_Ico] at _ht
                    exact heq (hOneJobPerTask t ht_range hbl cpu cpu0 jc jc0 h1 h2 hSameTask)
            simp [hFalse, heq]
        simp_rw [hAtMost1]
        rw [Finset.sum_ite_eq' Finset.univ cpu0 (fun _ => (1:ℕ))]
        simp
      · push_neg at hSched
        have : ∀ cpu : Fin num_cpus,
            (if task_scheduled_on job_task sched i cpu t = true then (1:ℕ) else 0) = 0 := by
          intro cpu; exact if_neg (hSched cpu)
        simp_rw [this]; simp
    · simp [hbl]

  -- ── Partition sum: Σ_hp x = Σ_hpE x + Σ_hpL x ──
  have hPartSum : (hp.map x_val).sum =
      (hpE.map x_val).sum + (hpL.map x_val).sum := by
    suffices ∀ L : List sporadic_task,
        (L.map x_val).sum =
        ((L.filter (fun i => decide (x_val i ≥ delta))).map x_val).sum +
        ((L.filter (fun i => decide (x_val i < delta))).map x_val).sum by
      exact this hp
    intro L; induction L with
    | nil => simp
    | cons hd tl ih =>
      simp only [List.map_cons, List.sum_cons, List.filter_cons]
      by_cases hge : x_val hd ≥ delta
      · have h1 : decide (x_val hd ≥ delta) = true := decide_eq_true_eq.mpr hge
        have h2 : decide (x_val hd < delta) = false := by
          simp only [decide_eq_false_iff_not, not_lt]; exact hge
        simp only [h1, h2, eq_self_iff_true, Bool.false_eq_true,
          ite_true, ite_false, ge_iff_le,
          List.map_cons, List.sum_cons] at ih ⊢
        omega
      · have h1 : decide (x_val hd ≥ delta) = false := decide_eq_false_iff_not.mpr hge
        have h2 : decide (x_val hd < delta) = true := by
          simp only [decide_eq_true_eq, GE.ge, not_le] at hge ⊢; exact hge
        simp only [h1, h2, eq_self_iff_true, Bool.false_eq_true,
          ite_true, ite_false, ge_iff_le,
          List.map_cons, List.sum_cons] at ih ⊢
        omega

  -- ── Σ_{hpE} x ≤ TI * k ──
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

  -- ── TI ≥ delta ──
  have hTI_ge_delta : TI ≥ delta := by
    have : hpE ≠ [] := by
      intro h
      have hHAS' : (0 : ℕ) < hpE.length := hHAS
      rw [h] at hHAS'; simp at hHAS'
    obtain ⟨tsk_a, hIn⟩ := List.exists_mem_of_ne_nil _ this
    have hge : x_val tsk_a ≥ delta := by
      exact of_decide_eq_true (List.mem_filter.mp hIn).2
    exact le_trans hge (hSingleLeTotal tsk_a (List.mem_of_mem_filter hIn))

  -- ── Combine: Σ_hpL x ≥ delta * (m - k) ──
  change (hpL.map (fun i => x_val i)).sum ≥ delta * (num_cpus - k)
  have hSumEq : (hpL.map x_val).sum = (hp.map x_val).sum - (hpE.map x_val).sum := by omega
  rw [hSumEq, hINV]
  -- Goal: TI * num_cpus - Σ_hpE x ≥ delta * (num_cpus - k)
  have hle : k ≤ num_cpus := le_of_lt hLT
  have hmul : TI * (num_cpus - k) + TI * k = TI * num_cpus := by
    rw [← Nat.left_distrib, Nat.sub_add_cancel hle]
  -- Now: delta * (m-k) ≤ TI * (m-k) and TI*(m-k) = TI*m - TI*k ≤ TI*m - Σ_hpE
  set a := TI * (num_cpus - k)
  set b := TI * k
  set c := (hpE.map x_val).sum
  set d := TI * num_cpus
  -- hmul: a + b = d, hExceedingBound: c ≤ b, hTI_ge_delta: TI ≥ delta
  -- Goal: d - c ≥ delta * (num_cpus - k)
  -- Since c ≤ b, d - c ≥ d - b = a = TI * (m-k) ≥ delta * (m-k)
  calc delta * (num_cpus - k)
      ≤ TI * (num_cpus - k) := Nat.mul_le_mul_right _ hTI_ge_delta
    _ ≤ d - c := by omega

include H_sporadic_tasks H_valid_job_parameters H_valid_task_parameters H_constrained_deadlines H_all_jobs_from_taskset H_jobs_come_from_arrival_sequence H_sequential_jobs H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_at_least_one_cpu H_work_conserving H_respects_FP_policy task_in_ts H_ts_nodup H_response_time_of_interfering_tasks_is_known H_hp_bounds_has_interfering_tasks H_response_time_bounds_ge_cost H_interfering_tasks_miss_no_deadlines H_response_time_no_larger_than_deadline H_j_arrives H_job_of_tsk H_j_not_completed H_previous_jobs_of_tsk_completed in
theorem bertogna_fp_minimum_exceeds_interference :
    ∀ (delta : ℕ),
      ((ts.filter (fun tsk_other =>
          higher_priority_task higher_eq_priority tsk tsk_other)).map
        (fun tsk_k => task_interference job_arrival job_cost job_task sched j tsk_k
          (job_arrival j) (job_arrival j + R))).sum ≥
      delta * num_cpus →
      ((ts.filter (fun tsk_other =>
          higher_priority_task higher_eq_priority tsk tsk_other)).map
        (fun tsk_k => min (task_interference job_arrival job_cost job_task sched j tsk_k
          (job_arrival j) (job_arrival j + R)) delta)).sum ≥
      delta * num_cpus := by
  intro delta hSum
  -- Abbreviations mirroring the Coq proof.
  set hp : List sporadic_task :=
    ts.filter (fun t => higher_priority_task higher_eq_priority tsk t) with hp_def
  set xval : sporadic_task → ℕ := fun tsk_k =>
    task_interference job_arrival job_cost job_task sched j tsk_k
      (job_arrival j) (job_arrival j + R) with xval_def
  change (hp.map xval).sum ≥ delta * num_cpus at hSum
  change (hp.map (fun i => min (xval i) delta)).sum ≥ delta * num_cpus
  -- Generic split lemma: partition a list by "xval i ≥ delta" vs "xval i < delta".
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
  -- Apply partition on xval (giving hSum structure) and on min (giving goal).
  have hSumSplit := hPart hp xval
  have hMinSplit := hPart hp (fun i => min (xval i) delta)
  -- Let k := # tasks exceeding delta, m := # tasks less than delta.
  set hpE : List sporadic_task := hp.filter (fun i => decide (delta ≤ xval i)) with hpE_def
  set hpL : List sporadic_task := hp.filter (fun i => decide (xval i < delta)) with hpL_def
  set k := hpE.length
  -- On hpE, xval ≥ delta, so min (xval i) delta = delta.
  have hEmin_eq :
      (hpE.map (fun i => min (xval i) delta)) =
      hpE.map (fun _ => delta) := by
    apply List.map_congr_left
    intro i hi
    have hmem : i ∈ hp ∧ decide (delta ≤ xval i) = true := by
      simpa [hpE_def, List.mem_filter] using hi
    have hle : delta ≤ xval i := of_decide_eq_true hmem.2
    exact min_eq_right hle
  -- On hpL, xval < delta, so min (xval i) delta = xval i.
  have hLmin_eq :
      (hpL.map (fun i => min (xval i) delta)) = hpL.map xval := by
    apply List.map_congr_left
    intro i hi
    have hmem : i ∈ hp ∧ decide (xval i < delta) = true := by
      simpa [hpL_def, List.mem_filter] using hi
    have hlt : xval i < delta := of_decide_eq_true hmem.2
    exact min_eq_left (le_of_lt hlt)
  -- Sum of constant delta = delta * length.
  have hEsum : (hpE.map (fun _ => delta)).sum = delta * k := by
    show (hpE.map (fun _ : sporadic_task => delta)).sum = delta * hpE.length
    rw [List.map_const', List.sum_replicate, smul_eq_mul, Nat.mul_comm]
  -- Also on hpE, xval i ≥ delta, so (hpE.map xval).sum ≥ delta * k.
  have hESum_xval_ge : (hpE.map xval).sum ≥ delta * k := by
    have hpw : ∀ i ∈ hpE, delta ≤ xval i := by
      intro i hi
      have : i ∈ hp ∧ decide (delta ≤ xval i) = true := by
        simpa [hpE_def, List.mem_filter] using hi
      exact of_decide_eq_true this.2
    -- Prove by induction.
    clear hEsum hEmin_eq hLmin_eq hSumSplit hMinSplit hSum
    show delta * k ≤ _
    simp only [k]
    clear_value hpE
    clear hpE_def
    induction hpE with
    | nil => simp
    | cons hd tl ih =>
      have hhd := hpw hd (List.mem_cons_self)
      have htl : ∀ i ∈ tl, delta ≤ xval i := fun i hi => hpw i (List.mem_cons_of_mem _ hi)
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.mul_succ]
      have := ih htl
      -- goal: delta * tl.length + delta ≤ xval hd + (tl.map xval).sum
      linarith [ih htl, hhd]
  -- Now do the 3-case analysis.
  rw [hMinSplit, hEmin_eq, hEsum, hLmin_eq]
  -- Goal: delta * k + (hpL.map xval).sum ≥ delta * num_cpus
  rcases Nat.lt_or_ge k num_cpus with hLT | hGE
  · rcases Nat.eq_zero_or_pos k with hZ | hPos
    · -- Case 1: k = 0. Then hpE is empty, so hpL.map xval sum = hp.map xval sum.
      have hpE_nil : hpE = [] := List.length_eq_zero_iff.mp hZ
      have hESum_zero : (hpE.map xval).sum = 0 := by rw [hpE_nil]; simp
      have : (hpL.map xval).sum = (hp.map xval).sum := by
        rw [hSumSplit, hESum_zero]; ring
      rw [this]
      simp [hZ]
      exact hSum
    · -- Case 3: 0 < k < num_cpus. Apply non_full_processors.
      have hNFP :=
        bertogna_fp_interference_in_non_full_processors task_cost task_period task_deadline
          job_arrival job_cost job_deadline job_task arr_seq H_sporadic_tasks
          H_valid_job_parameters ts H_valid_task_parameters H_constrained_deadlines
          H_all_jobs_from_taskset (num_cpus := num_cpus) sched
          H_jobs_come_from_arrival_sequence H_sequential_jobs H_jobs_must_arrive_to_execute
          H_completed_jobs_dont_execute H_at_least_one_cpu higher_eq_priority
          H_work_conserving H_respects_FP_policy tsk task_in_ts H_ts_nodup hp_bounds
          H_response_time_of_interfering_tasks_is_known H_hp_bounds_has_interfering_tasks
          H_response_time_bounds_ge_cost H_interfering_tasks_miss_no_deadlines R
          H_response_time_no_larger_than_deadline
          j H_j_arrives H_job_of_tsk H_j_not_completed H_previous_jobs_of_tsk_completed
          delta ⟨hPos, hLT⟩
      -- hNFP : (hp.filter (x < delta)).map x .sum ≥ delta * (num_cpus - k)
      -- Note: the let-bindings in hNFP need unfolding; it should be about hpL
      change (hpL.map xval).sum ≥ delta * (num_cpus - k) at hNFP
      -- delta * k + delta * (num_cpus - k) = delta * num_cpus since k ≤ num_cpus
      have hsum_eq : delta * k + delta * (num_cpus - k) = delta * num_cpus := by
        rw [← Nat.mul_add, Nat.add_sub_cancel' (le_of_lt hLT)]
      linarith
  · -- Case 2: k ≥ num_cpus. Then delta * k ≥ delta * num_cpus.
    have : delta * num_cpus ≤ delta * k := Nat.mul_le_mul_left delta hGE
    linarith [Nat.zero_le ((hpL.map xval).sum)]

include H_sporadic_tasks H_valid_job_parameters H_valid_task_parameters H_constrained_deadlines H_all_jobs_from_taskset H_jobs_come_from_arrival_sequence H_sequential_jobs H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_at_least_one_cpu H_work_conserving H_respects_FP_policy task_in_ts H_ts_nodup H_response_time_of_interfering_tasks_is_known H_hp_bounds_has_interfering_tasks H_response_time_bounds_ge_cost H_interfering_tasks_miss_no_deadlines H_response_time_recurrence_holds H_response_time_no_larger_than_deadline H_j_arrives H_job_of_tsk H_j_not_completed H_previous_jobs_of_tsk_completed in
theorem bertogna_fp_sum_exceeds_total_interference :
    (hp_bounds.map (fun tsk_R =>
      min (task_interference job_arrival job_cost job_task sched j tsk_R.1
        (job_arrival j) (job_arrival j + R))
        (R - task_cost tsk + 1))).sum >
    total_interference_bound_fp task_cost task_period tsk hp_bounds R := by
  -- Abbreviations
  set x : sporadic_task → ℕ := fun k =>
    task_interference job_arrival job_cost job_task sched j k
      (job_arrival j) (job_arrival j + R) with x_def
  set c := task_cost tsk with c_def
  set delta := R - c + 1 with delta_def
  set N := total_interference_bound_fp task_cost task_period tsk hp_bounds R with N_def
  set hp_tasks := ts.filter (fun t =>
    higher_priority_task higher_eq_priority tsk t) with hp_tasks_def
  -- Step A: From recurrence, R = c + N / num_cpus, so N < delta * num_cpus.
  have hRec : R = c + N / num_cpus := by
    have h := H_response_time_recurrence_holds
    unfold div_floor at h; exact h
  have hCleR : c ≤ R := by rw [hRec]; exact Nat.le_add_right _ _
  have hDivEq : N / num_cpus = R - c := by
    rw [hRec, Nat.add_sub_cancel_left]
  have hNlt : N < delta * num_cpus := by
    have hmod := Nat.div_add_mod N num_cpus
    have hmod_lt : N % num_cpus < num_cpus := Nat.mod_lt N H_at_least_one_cpu
    have hcpos : 0 < num_cpus := H_at_least_one_cpu
    have hDelta_eq : delta = N / num_cpus + 1 := by
      rw [delta_def, hDivEq]
    -- N = num_cpus * (N / num_cpus) + N % num_cpus < num_cpus * (N / num_cpus + 1)
    --   = (N / num_cpus + 1) * num_cpus = delta * num_cpus
    rw [hDelta_eq, Nat.add_mul, Nat.one_mul, Nat.mul_comm]
    omega
  -- Step B: ALLBUSY — sum over hp_tasks of x_k = X * num_cpus
  have hAllBusy :=
    bertogna_fp_interference_on_all_cpus task_cost task_period task_deadline
      job_arrival job_cost job_deadline job_task arr_seq H_sporadic_tasks
      H_valid_job_parameters ts H_valid_task_parameters H_constrained_deadlines
      H_all_jobs_from_taskset (num_cpus := num_cpus) sched
      H_jobs_come_from_arrival_sequence H_sequential_jobs H_jobs_must_arrive_to_execute
      H_completed_jobs_dont_execute H_at_least_one_cpu higher_eq_priority
      H_work_conserving H_respects_FP_policy tsk task_in_ts H_ts_nodup hp_bounds
      H_response_time_of_interfering_tasks_is_known H_hp_bounds_has_interfering_tasks
      H_response_time_bounds_ge_cost H_interfering_tasks_miss_no_deadlines R
      H_response_time_no_larger_than_deadline
      j H_j_arrives H_job_of_tsk H_j_not_completed H_previous_jobs_of_tsk_completed
  -- Step C: TOOMUCH — X ≥ R - c + 1 = delta
  have hTooMuch :=
    bertogna_fp_too_much_interference task_cost task_period task_deadline
      job_arrival job_cost job_deadline job_task arr_seq H_sporadic_tasks
      H_valid_job_parameters ts H_valid_task_parameters H_constrained_deadlines
      H_all_jobs_from_taskset (num_cpus := num_cpus) sched
      H_jobs_come_from_arrival_sequence H_sequential_jobs H_jobs_must_arrive_to_execute
      H_completed_jobs_dont_execute H_at_least_one_cpu higher_eq_priority
      H_work_conserving H_respects_FP_policy tsk hp_bounds
      H_response_time_of_interfering_tasks_is_known H_hp_bounds_has_interfering_tasks
      H_response_time_bounds_ge_cost H_interfering_tasks_miss_no_deadlines R
      H_response_time_recurrence_holds H_response_time_no_larger_than_deadline
      j H_j_arrives H_job_of_tsk H_j_not_completed H_previous_jobs_of_tsk_completed
  -- Step D: Combine: sum hp_tasks x_k ≥ delta * num_cpus
  have hSumHP_ge : (hp_tasks.map x).sum ≥ delta * num_cpus := by
    change (hp_tasks.map x).sum ≥ (R - c + 1) * num_cpus
    rw [hAllBusy]
    exact Nat.mul_le_mul_right _ hTooMuch
  -- Step E: Apply minimum_exceeds_interference
  have hMinHP :=
    bertogna_fp_minimum_exceeds_interference task_cost task_period task_deadline
      job_arrival job_cost job_deadline job_task arr_seq H_sporadic_tasks
      H_valid_job_parameters ts H_valid_task_parameters H_constrained_deadlines
      H_all_jobs_from_taskset (num_cpus := num_cpus) sched
      H_jobs_come_from_arrival_sequence H_sequential_jobs H_jobs_must_arrive_to_execute
      H_completed_jobs_dont_execute H_at_least_one_cpu higher_eq_priority
      H_work_conserving H_respects_FP_policy tsk task_in_ts H_ts_nodup hp_bounds
      H_response_time_of_interfering_tasks_is_known H_hp_bounds_has_interfering_tasks
      H_response_time_bounds_ge_cost H_interfering_tasks_miss_no_deadlines R
      H_response_time_no_larger_than_deadline
      j H_j_arrives H_job_of_tsk H_j_not_completed H_previous_jobs_of_tsk_completed
      delta hSumHP_ge
  -- Step F: Bridge hp_bounds → hp_tasks via witness injection.
  have hp_tasks_nodup : hp_tasks.Nodup := List.Nodup.filter _ H_ts_nodup
  have hHas : ∀ t ∈ hp_tasks, ∃ R', (t, R') ∈ hp_bounds := by
    intro t ht
    rw [hp_tasks_def, List.mem_filter] at ht
    exact H_hp_bounds_has_interfering_tasks t ht.1 ht.2
  choose pickR hPickMem using hHas
  -- Witness list: pairs (t, pickR t) for each t ∈ hp_tasks.
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
  -- sum over witList of g = sum over hp_tasks of g ∘ (·, pickR ·)
  have hWit_sum :
      (witList.map (fun p => min (x p.1) delta)).sum =
      (hp_tasks.map (fun t => min (x t) delta)).sum := by
    show ((hp_tasks.attach.map _).map _).sum = _
    rw [List.map_map]
    -- Rewrite hp_tasks = hp_tasks.attach.map (·.val)
    conv_rhs => rw [show hp_tasks = hp_tasks.attach.map (·.val) from
      (hp_tasks.attach_map_subtype_val).symm]
    rw [List.map_map]
    rfl
  -- Multiset ≤ : via Nodup.subperm
  have hMs : (↑witList : Multiset (sporadic_task × Time)) ≤ (↑hp_bounds : Multiset _) := by
    rw [Multiset.coe_le]
    exact hWit_nodup.subperm hWit_sub
  -- Map and split: hp_bounds = witList + (hp_bounds - witList) as multisets.
  have hSplit : (↑hp_bounds : Multiset (sporadic_task × Time)) =
      (↑witList : Multiset (sporadic_task × Time)) +
        ((↑hp_bounds : Multiset (sporadic_task × Time)) -
         (↑witList : Multiset (sporadic_task × Time))) := by
    exact (tsub_add_cancel_of_le hMs).symm.trans (add_comm _ _)
  have hBridge :
      (hp_tasks.map (fun t => min (x t) delta)).sum ≤
      (hp_bounds.map (fun p : sporadic_task × Time => min (x p.1) delta)).sum := by
    rw [← hWit_sum]
    show (Multiset.map (fun p : sporadic_task × Time => min (x p.1) delta)
            (↑witList : Multiset (sporadic_task × Time))).sum ≤
         (Multiset.map (fun p : sporadic_task × Time => min (x p.1) delta)
            (↑hp_bounds : Multiset (sporadic_task × Time))).sum
    rw [hSplit, Multiset.map_add, Multiset.sum_add]
    exact Nat.le_add_right _ _
  -- Final: sum_hp_bounds ≥ sum_hp_tasks min ≥ delta * num_cpus > N
  calc (hp_bounds.map (fun tsk_R => min (x tsk_R.1) delta)).sum
      ≥ (hp_tasks.map (fun t => min (x t) delta)).sum := hBridge
    _ ≥ delta * num_cpus := hMinHP
    _ > N := hNlt

include H_sporadic_tasks H_valid_job_parameters H_valid_task_parameters H_constrained_deadlines H_all_jobs_from_taskset H_jobs_come_from_arrival_sequence H_sequential_jobs H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_at_least_one_cpu H_work_conserving H_respects_FP_policy task_in_ts H_ts_nodup H_response_time_of_interfering_tasks_is_known H_hp_bounds_has_interfering_tasks H_response_time_bounds_ge_cost H_interfering_tasks_miss_no_deadlines H_response_time_recurrence_holds H_response_time_no_larger_than_deadline H_j_arrives H_job_of_tsk H_j_not_completed H_previous_jobs_of_tsk_completed in
theorem bertogna_fp_exists_task_that_exceeds_bound :
    ∃ tsk_k R_k,
      (tsk_k, R_k) ∈ hp_bounds ∧
      min (task_interference job_arrival job_cost job_task sched j tsk_k
        (job_arrival j) (job_arrival j + R)) (R - task_cost tsk + 1) >
      min (W task_cost task_period tsk_k R_k R) (R - task_cost tsk + 1) := by
  -- Coq strategy: by contradiction; suppose all min x ≤ min W. Then sum
  -- of min x ≤ sum of min W = total_interference_bound_fp, contradicting
  -- bertogna_fp_sum_exceeds_total_interference.
  by_contra hAll
  push_neg at hAll
  -- hAll : ∀ tsk_k R_k, (tsk_k, R_k) ∈ hp_bounds →
  --        min (x tsk_k) (R - task_cost tsk + 1) ≤ min (W ...) (R - task_cost tsk + 1)
  have hSum :=
    bertogna_fp_sum_exceeds_total_interference task_cost task_period task_deadline
      job_arrival job_cost job_deadline job_task arr_seq H_sporadic_tasks
      H_valid_job_parameters ts H_valid_task_parameters H_constrained_deadlines
      H_all_jobs_from_taskset (num_cpus := num_cpus) sched
      H_jobs_come_from_arrival_sequence H_sequential_jobs H_jobs_must_arrive_to_execute
      H_completed_jobs_dont_execute H_at_least_one_cpu higher_eq_priority
      H_work_conserving H_respects_FP_policy tsk task_in_ts H_ts_nodup hp_bounds
      H_response_time_of_interfering_tasks_is_known H_hp_bounds_has_interfering_tasks
      H_response_time_bounds_ge_cost H_interfering_tasks_miss_no_deadlines R
      H_response_time_recurrence_holds H_response_time_no_larger_than_deadline
      j H_j_arrives H_job_of_tsk H_j_not_completed H_previous_jobs_of_tsk_completed
  -- LHS ≤ Σ min W = total_interference_bound_fp.
  have hSumLe : ∀ (L : List (sporadic_task × Time)),
      (∀ p ∈ L, min (task_interference job_arrival job_cost job_task sched j p.1
                      (job_arrival j) (job_arrival j + R)) (R - task_cost tsk + 1) ≤
                  min (W task_cost task_period p.1 p.2 R) (R - task_cost tsk + 1)) →
      (L.map (fun tsk_R => min (task_interference job_arrival job_cost job_task sched j tsk_R.1
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
  have hLe := hSumLe hp_bounds (fun p hMem => hAll p.1 p.2 (by cases p; exact hMem))
  -- RHS = total_interference_bound_fp by definition.
  have hEq :
      (hp_bounds.map (fun tsk_R => min (W task_cost task_period tsk_R.1 tsk_R.2 R)
        (R - task_cost tsk + 1))).sum =
      total_interference_bound_fp task_cost task_period tsk hp_bounds R := by
    unfold total_interference_bound_fp interference_bound_generic
    rfl
  rw [hEq] at hLe
  exact absurd hSum (not_lt.mpr hLe)

end DerivingContradiction

end Lemmas

include H_sporadic_tasks H_valid_job_parameters H_valid_task_parameters
  H_constrained_deadlines H_all_jobs_from_taskset H_jobs_come_from_arrival_sequence
  H_completed_jobs_dont_execute H_jobs_must_arrive_to_execute H_sequential_jobs
  H_at_least_one_cpu H_work_conserving H_respects_FP_policy
  H_response_time_of_interfering_tasks_is_known H_hp_bounds_has_interfering_tasks
  H_response_time_bounds_ge_cost H_interfering_tasks_miss_no_deadlines
  H_response_time_recurrence_holds H_response_time_no_larger_than_deadline
  task_in_ts

include H_sporadic_tasks H_valid_job_parameters H_valid_task_parameters H_constrained_deadlines H_all_jobs_from_taskset H_jobs_come_from_arrival_sequence H_sequential_jobs H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_at_least_one_cpu H_work_conserving H_respects_FP_policy task_in_ts H_ts_nodup H_response_time_of_interfering_tasks_is_known H_hp_bounds_has_interfering_tasks H_response_time_bounds_ge_cost H_interfering_tasks_miss_no_deadlines H_response_time_recurrence_holds H_response_time_no_larger_than_deadline in
theorem bertogna_cirinei_response_time_bound_fp :
    is_response_time_bound_of_task job_arrival job_cost job_task arr_seq sched tsk R := by
  -- Coq strategy: strong induction on `job_arrival j + R`. The IH provides
  -- "previous jobs of tsk are completed by their bound" (BEFOREok). By
  -- contradiction, assume j not completed at arr+R. Apply exists_task to get
  -- some (tsk_k, R_k) with min(x, R-c+1) > min(W, R-c+1). But workload_bounds
  -- gives x ≤ W, hence min(x,_) ≤ min(W,_) — contradiction.
  suffices H : ∀ n, ∀ (j : Job), arrives_in arr_seq j → job_task j = tsk →
      job_arrival j + R = n → completed job_cost sched j (job_arrival j + R) by
    intro j hARR hJOB; exact H _ j hARR hJOB rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro j hARR hJOB hEqN
    by_contra hNCOMP
    -- Derive previous-jobs property from IH.
    have hPREV : ∀ j0, arrives_in arr_seq j0 → job_task j0 = tsk →
        job_arrival j0 < job_arrival j →
        completed job_cost sched j0 (job_arrival j0 + R) := by
      intro j0 hARR0 hJOB0 hLT0
      refine IH (job_arrival j0 + R) ?_ j0 hARR0 hJOB0 rfl
      simp only [Time] at *; omega
    -- Apply exists_task.
    obtain ⟨tsk_k, R_k, hMem, hMinGT⟩ :=
      bertogna_fp_exists_task_that_exceeds_bound task_cost task_period task_deadline
        job_arrival job_cost job_deadline job_task arr_seq H_sporadic_tasks
        H_valid_job_parameters ts H_valid_task_parameters H_constrained_deadlines
        H_all_jobs_from_taskset (num_cpus := num_cpus) sched
        H_jobs_come_from_arrival_sequence H_sequential_jobs H_jobs_must_arrive_to_execute
        H_completed_jobs_dont_execute H_at_least_one_cpu higher_eq_priority
        H_work_conserving H_respects_FP_policy tsk task_in_ts H_ts_nodup hp_bounds
        H_response_time_of_interfering_tasks_is_known H_hp_bounds_has_interfering_tasks
        H_response_time_bounds_ge_cost H_interfering_tasks_miss_no_deadlines R
        H_response_time_recurrence_holds H_response_time_no_larger_than_deadline
        j hARR hJOB hNCOMP hPREV
    -- Apply workload_bounds_interference for this (tsk_k, R_k).
    have hWB :=
      bertogna_fp_workload_bounds_interference task_cost task_period task_deadline
        job_arrival job_cost job_deadline job_task arr_seq H_sporadic_tasks
        H_valid_job_parameters ts H_valid_task_parameters H_constrained_deadlines
        H_all_jobs_from_taskset (num_cpus := num_cpus) sched
        H_jobs_come_from_arrival_sequence H_sequential_jobs H_jobs_must_arrive_to_execute
        H_completed_jobs_dont_execute H_at_least_one_cpu higher_eq_priority
        H_work_conserving H_respects_FP_policy tsk hp_bounds
        H_response_time_of_interfering_tasks_is_known H_hp_bounds_has_interfering_tasks
        H_response_time_bounds_ge_cost H_interfering_tasks_miss_no_deadlines R
        H_response_time_no_larger_than_deadline
        j hARR hJOB hNCOMP hPREV tsk_k R_k hMem
    -- min(x, c) ≤ min(W, c), contradicting hMinGT.
    exact absurd hMinGT (not_lt.mpr (min_le_min_right _ hWB))

end ResponseTimeBound

end ResponseTimeAnalysisFP

end Prosa.Classic.Analysis.Global.Basic.Bertogna_fp_theory
