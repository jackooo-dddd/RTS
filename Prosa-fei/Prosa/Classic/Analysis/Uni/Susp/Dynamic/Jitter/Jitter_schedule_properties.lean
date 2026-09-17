-- Translated from: ../rt-proofs/classic/analysis/uni/susp/dynamic/jitter/jitter_schedule_properties.v
import Prosa.Classic.Util.All
import Prosa.Classic.Model.Priority
import Prosa.Classic.Model.Arrival.Basic.Job
import Prosa.Classic.Model.Arrival.Jitter.Job
import Prosa.Classic.Model.Schedule.Uni.Schedulability
import Prosa.Classic.Model.Schedule.Uni.Jitter.Schedule
import Prosa.Classic.Model.Schedule.Uni.Jitter.Valid_schedule
import Prosa.Classic.Model.Schedule.Uni.Jitter.Platform
import Prosa.Classic.Model.Schedule.Uni.Susp.Suspension_intervals
import Prosa.Classic.Model.Schedule.Uni.Response_time
import Prosa.Classic.Analysis.Uni.Susp.Dynamic.Jitter.Jitter_schedule
import Prosa.Classic.Model.Schedule.Uni.Transformation.Construction

noncomputable section

namespace Prosa.Classic.Analysis.Uni.Susp.Dynamic.Jitter.Jitter_schedule_properties

open Prosa.Classic.Model.Time
open Prosa.Classic.Model.Schedule.Uni.Schedule
open Prosa.Classic.Model.Schedule.Uni.Jitter.Schedule
open Prosa.Classic.Model.Schedule.Uni.Jitter.Platform.Platform
open Prosa.Classic.Model.Schedule.Uni.Jitter.Valid_schedule.ValidJitterAwareSchedule
open Prosa.Classic.Model.Arrival.Basic.Arrival_sequence
open Prosa.Classic.Model.Arrival.Jitter.Arrival_sequence
open Prosa.Classic.Model.Priority
open Prosa.Classic.Model.Suspension
open Prosa.Classic.Model.Schedule.Uni.Susp.Suspension_intervals
open Prosa.Classic.Model.Schedule.Uni.Response_time.ResponseTime
open Prosa.Classic.Model.Schedule.Uni.Transformation.Construction.ScheduleConstruction
open Prosa.Classic.Analysis.Uni.Susp.Dynamic.Jitter.Jitter_schedule.JitterScheduleConstruction
open Prosa.Classic.Util.Minmax

namespace JitterScheduleProperties

section ProvingScheduleProperties

variable {Task : Type _} [DecidableEq Task]
variable {Job : Type _} [DecidableEq Job]
variable (job_arrival : Job → Time)
variable (job_task : Job → Task)

variable (ts : List Task)

variable (arr_seq : arrival_sequence Job)
variable (H_arrival_times_are_consistent :
  arrival_times_are_consistent job_arrival arr_seq)

variable (H_jobs_from_taskset :
  ∀ j, arrives_in arr_seq j → job_task j ∈ ts)

variable (higher_eq_priority : FP_policy Task)
variable (H_priority_is_reflexive : FP_is_reflexive higher_eq_priority)
variable (H_priority_is_transitive : FP_is_transitive higher_eq_priority)
variable (H_priority_is_total : FP_is_total_over_task_set higher_eq_priority ts)

private def job_higher_eq_priority : JLDP_policy Job :=
  FP_to_JLDP job_task higher_eq_priority

variable (job_cost : Job → Time)
variable (task_cost : Task → Time)

variable (job_suspension_duration : job_suspension Job)

variable (sched_susp : schedule Job)
variable (H_valid_schedule :
  jobs_come_from_arrival_sequence sched_susp arr_seq ∧
  jobs_must_arrive_to_execute job_arrival sched_susp ∧
  completed_jobs_dont_execute job_cost sched_susp ∧
  True)

private def job_response_time_in_sched_susp_bounded_by (j : Job) (R : Time) : Prop :=
  is_response_time_bound_of_job job_arrival job_cost sched_susp j R

variable (j : Job)
variable (H_from_arrival_sequence : arrives_in arr_seq j)

private def arr_j : Time := job_arrival j
private def task_of_j : Task := job_task j

private def other_hep_task (tsk_other : Task) : Bool :=
  higher_eq_priority tsk_other (job_task j) && decide (tsk_other ≠ job_task j)

variable (R : Job → Time)

private def sched_jitter_local : schedule Job :=
  sched_jitter job_arrival job_task higher_eq_priority job_cost job_suspension_duration arr_seq j R

private def inflated_job_cost_local : Job → Time :=
  inflated_job_cost job_cost job_suspension_duration j

private def job_jitter_local : Job → Time :=
  job_jitter job_arrival job_task higher_eq_priority job_cost j R

section PropertiesOfScheduleConstruction

private def build_schedule_local : schedule Job → Time → Option Job :=
  build_schedule job_arrival job_task higher_eq_priority job_cost job_suspension_duration arr_seq j R

theorem sched_jitter_depends_only_on_service :
    ∀ sched1 sched2 t,
      (∀ j, service sched1 j t = service sched2 j t) →
      build_schedule_local job_arrival job_task arr_seq higher_eq_priority
        job_cost job_suspension_duration j R sched1 t =
      build_schedule_local job_arrival job_task arr_seq higher_eq_priority
        job_cost job_suspension_duration j R sched2 t := by
  intro sched1 sched2 t ALL
  simp only [build_schedule_local, build_schedule, highest_priority_job_other_than_j,
             pending_jobs_other_than_j]
  have SAME_PEND : ∀ j0,
      (decide (actual_arrival job_arrival (job_jitter job_arrival job_task higher_eq_priority job_cost j R) j0 ≤ t) &&
       !decide (inflated_job_cost job_cost job_suspension_duration j j0 ≤ service sched1 j0 t)) =
      (decide (actual_arrival job_arrival (job_jitter job_arrival job_task higher_eq_priority job_cost j R) j0 ≤ t) &&
       !decide (inflated_job_cost job_cost job_suspension_duration j j0 ≤ service sched2 j0 t)) := by
    intro j0; congr 1; congr 1; simp [ALL j0]
  have SAME_FILTER :
    List.filter
      (fun j_other =>
        decide (actual_arrival job_arrival (job_jitter job_arrival job_task higher_eq_priority job_cost j R) j_other ≤ t) &&
        !decide (inflated_job_cost job_cost job_suspension_duration j j_other ≤ service sched1 j_other t) &&
        decide (j_other ≠ j))
      (actual_arrivals_up_to job_arrival (job_jitter job_arrival job_task higher_eq_priority job_cost j R) arr_seq t) =
    List.filter
      (fun j_other =>
        decide (actual_arrival job_arrival (job_jitter job_arrival job_task higher_eq_priority job_cost j R) j_other ≤ t) &&
        !decide (inflated_job_cost job_cost job_suspension_duration j j_other ≤ service sched2 j_other t) &&
        decide (j_other ≠ j))
      (actual_arrivals_up_to job_arrival (job_jitter job_arrival job_task higher_eq_priority job_cost j R) arr_seq t) := by
    congr 1; ext j0; congr 1; exact SAME_PEND j0
  rw [SAME_FILTER, SAME_PEND j]

theorem sched_jitter_uses_construction_function :
    ∀ t,
      sched_jitter_local job_arrival job_task arr_seq higher_eq_priority
        job_cost job_suspension_duration j R t =
      build_schedule_local job_arrival job_task arr_seq higher_eq_priority
        job_cost job_suspension_duration j R
        (sched_jitter_local job_arrival job_task arr_seq higher_eq_priority
          job_cost job_suspension_duration j R) t := by
  intro t
  exact service_dependent_schedule_construction
    (build_schedule job_arrival job_task higher_eq_priority job_cost
      job_suspension_duration arr_seq j R)
    (fun _ => none)
    (sched_jitter_depends_only_on_service job_arrival job_task arr_seq higher_eq_priority
      job_cost job_suspension_duration j R) t

end PropertiesOfScheduleConstruction

section ScheduleIsValid

include H_arrival_times_are_consistent H_from_arrival_sequence in
theorem sched_jitter_jobs_come_from_arrival_sequence :
    jobs_come_from_arrival_sequence
      (sched_jitter_local job_arrival job_task arr_seq higher_eq_priority
        job_cost job_suspension_duration j R)
      arr_seq := by
  intro j0 t SCHED
  have USE := sched_jitter_uses_construction_function job_arrival job_task arr_seq higher_eq_priority
    job_cost job_suspension_duration j R t
  simp only [sched_jitter_local, build_schedule_local] at USE SCHED
  simp only [scheduled_at] at SCHED
  rw [USE] at SCHED
  simp only [build_schedule, highest_priority_job_other_than_j] at SCHED
  set sched_j := sched_jitter job_arrival job_task higher_eq_priority job_cost job_suspension_duration arr_seq j R
  set jj := job_jitter job_arrival job_task higher_eq_priority job_cost j R
  set pend_j := (decide (actual_arrival job_arrival jj j ≤ t) &&
    !decide (inflated_job_cost job_cost job_suspension_duration j j ≤ service sched_j j t))
  set hp := seq_min (FP_to_JLFP job_task higher_eq_priority)
    (pending_jobs_other_than_j job_arrival job_task higher_eq_priority job_cost
      job_suspension_duration arr_seq j R sched_j t)
  have hp_arrives : ∀ j_hp, j_hp ∈ pending_jobs_other_than_j job_arrival job_task higher_eq_priority
      job_cost job_suspension_duration arr_seq j R sched_j t →
      arrives_in arr_seq j_hp := by
    intro j_hp h_in
    simp only [pending_jobs_other_than_j] at h_in
    have h_mem := List.mem_of_mem_filter h_in
    exact in_actual_arrivals_between_implies_arrived job_arrival jj arr_seq
      H_arrival_times_are_consistent j_hp 0 (t + 1) h_mem
  by_cases hpend : pend_j = true
  · simp only [hpend, ↑reduceIte] at SCHED
    cases hp_val : hp with
    | none =>
      simp only [hp_val] at SCHED
      have := (Option.some_injective _ (beq_iff_eq.mp SCHED)).symm; subst this
      exact H_from_arrival_sequence
    | some j_hp =>
      simp only [hp_val] at SCHED
      split_ifs at SCHED with hprio
      · have h_eq := (Option.some_injective _ (beq_iff_eq.mp SCHED)).symm
        rw [h_eq]
        exact H_from_arrival_sequence
      · have h_eq := (Option.some_injective _ (beq_iff_eq.mp SCHED)).symm
        rw [h_eq]
        exact hp_arrives _ (seq_min_in_seq (FP_to_JLFP job_task higher_eq_priority) _ _ hp_val)
  · simp only [Bool.not_eq_true] at hpend
    simp only [hpend, Bool.false_eq_true, ↑reduceIte] at SCHED
    cases hp_val : hp with
    | none => simp [hp_val] at SCHED
    | some j_hp =>
      simp only [hp_val] at SCHED
      have h_eq := (Option.some_injective _ (beq_iff_eq.mp SCHED)).symm
      rw [h_eq]
      exact hp_arrives _ (seq_min_in_seq (FP_to_JLFP job_task higher_eq_priority) _ _ hp_val)

theorem sched_jitter_jobs_execute_after_jitter :
    jobs_execute_after_jitter job_arrival
      (job_jitter_local job_arrival job_task higher_eq_priority job_cost j R)
      (sched_jitter_local job_arrival job_task arr_seq higher_eq_priority
        job_cost job_suspension_duration j R) := by
  intro j0 t SCHED
  have USE := sched_jitter_uses_construction_function job_arrival job_task arr_seq higher_eq_priority
    job_cost job_suspension_duration j R t
  simp only [sched_jitter_local, build_schedule_local, job_jitter_local] at USE SCHED ⊢
  simp only [scheduled_at] at SCHED
  rw [USE] at SCHED
  simp only [build_schedule, highest_priority_job_other_than_j] at SCHED
  set sched_j := sched_jitter job_arrival job_task higher_eq_priority job_cost job_suspension_duration arr_seq j R
  set jj := job_jitter job_arrival job_task higher_eq_priority job_cost j R
  set pend_j := (decide (actual_arrival job_arrival jj j ≤ t) &&
    !decide (inflated_job_cost job_cost job_suspension_duration j j ≤ service sched_j j t))
  set hp := seq_min (FP_to_JLFP job_task higher_eq_priority)
    (pending_jobs_other_than_j job_arrival job_task higher_eq_priority job_cost
      job_suspension_duration arr_seq j R sched_j t)
  -- Helper: jitter_has_passed for jobs from pending_jobs_other_than_j
  have hp_jitter : ∀ j_hp, j_hp ∈ pending_jobs_other_than_j job_arrival job_task higher_eq_priority
      job_cost job_suspension_duration arr_seq j R sched_j t →
      jitter_has_passed job_arrival jj j_hp t := by
    intro j_hp h_in
    simp only [pending_jobs_other_than_j] at h_in
    have h_filter := List.of_mem_filter h_in
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
      decide_eq_false_iff_not, not_le] at h_filter
    exact h_filter.1.1
  by_cases hpend : pend_j = true
  · simp only [hpend, ↓reduceIte] at SCHED
    cases hp_val : hp with
    | none =>
      simp only [hp_val] at SCHED
      have := (Option.some_injective _ (beq_iff_eq.mp SCHED)).symm; subst this
      simp only [pend_j, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
        decide_eq_false_iff_not, not_le] at hpend
      exact hpend.1
    | some j_hp =>
      simp only [hp_val] at SCHED
      split_ifs at SCHED with hprio
      · have h_eq := (Option.some_injective _ (beq_iff_eq.mp SCHED)).symm
        rw [h_eq]
        simp only [pend_j, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
          decide_eq_false_iff_not, not_le] at hpend
        exact hpend.1
      · have h_eq := (Option.some_injective _ (beq_iff_eq.mp SCHED)).symm
        rw [h_eq]
        exact hp_jitter _ (seq_min_in_seq (FP_to_JLFP job_task higher_eq_priority) _ _ hp_val)
  · simp only [Bool.not_eq_true] at hpend
    simp only [hpend, Bool.false_eq_true, ↓reduceIte] at SCHED
    cases hp_val : hp with
    | none => simp [hp_val] at SCHED
    | some j_hp =>
      simp only [hp_val] at SCHED
      have h_eq := (Option.some_injective _ (beq_iff_eq.mp SCHED)).symm
      rw [h_eq]
      exact hp_jitter _ (seq_min_in_seq (FP_to_JLFP job_task higher_eq_priority) _ _ hp_val)

theorem sched_jitter_completed_jobs_dont_execute :
    completed_jobs_dont_execute
      (inflated_job_cost_local job_cost job_suspension_duration j)
      (sched_jitter_local job_arrival job_task arr_seq higher_eq_priority
        job_cost job_suspension_duration j R) := by
  simp only [completed_jobs_dont_execute, inflated_job_cost_local, sched_jitter_local]
  intro j0 t
  set sched_j := sched_jitter job_arrival job_task higher_eq_priority job_cost job_suspension_duration arr_seq j R
  induction t with
  | zero =>
    simp only [service, service_during, Finset.Ico_self, Finset.sum_empty]
    exact Nat.zero_le _
  | succ n ih =>
    -- Prove service(n+1) ≤ inflated_cost(j0) using IH and construction property
    -- Key: if service_at(n) = 0 then easy from IH. If service_at(n) = 1 then j0 scheduled at n,
    -- and the construction only schedules non-completed jobs, so service(n) < inflated_cost(j0).
    simp only [service, service_during]
    rw [Finset.sum_Ico_succ_top (Nat.zero_le n)]
    by_cases h_sa : service_at sched_j j0 n = 0
    · simp only [service, service_during] at ih; rw [h_sa]; omega
    · have h_sa_le := service_at_most_one sched_j j0 n
      have h_sa_eq : service_at sched_j j0 n = 1 := by omega
      -- j0 is scheduled at n, so sched_j n = some j0
      have h_eq_j0 : sched_j n = some j0 := by
        simp only [service_at, scheduled_at] at h_sa_eq
        by_contra h_ne
        have hf : (sched_j n == some j0) = false := by
          rw [beq_eq_false_iff_ne]; exact h_ne
        simp [hf, Bool.toNat] at h_sa_eq
      -- Use the construction function property
      have USE := sched_jitter_uses_construction_function job_arrival job_task arr_seq higher_eq_priority
        job_cost job_suspension_duration j R n
      simp only [sched_jitter_local, build_schedule_local] at USE
      change sched_j n = _ at USE
      rw [USE] at h_eq_j0
      simp only [build_schedule, highest_priority_job_other_than_j] at h_eq_j0
      set jj := job_jitter job_arrival job_task higher_eq_priority job_cost j R
      set pend_val := (decide (actual_arrival job_arrival jj j ≤ n) &&
        !decide (inflated_job_cost job_cost job_suspension_duration j j ≤ service sched_j j n))
      set hp := seq_min (FP_to_JLFP job_task higher_eq_priority)
        (pending_jobs_other_than_j job_arrival job_task higher_eq_priority job_cost
          job_suspension_duration arr_seq j R sched_j n)
      -- Show j0 is not completed at n
      suffices h_lt : ∑ i ∈ Finset.Ico 0 n, service_at sched_j j0 i < inflated_job_cost job_cost job_suspension_duration j j0 by
        rw [h_sa_eq]; simp only [service, service_during] at ih; omega
      by_cases hpend : pend_val = true
      · simp only [hpend, ↓reduceIte] at h_eq_j0
        cases hp_val : hp with
        | none =>
          simp only [hp_val] at h_eq_j0
          have := (Option.some_injective _ h_eq_j0).symm; subst this
          simp only [pend_val, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
            decide_eq_false_iff_not, not_le] at hpend
          exact hpend.2
        | some j_hp =>
          simp only [hp_val] at h_eq_j0
          split_ifs at h_eq_j0 with hprio
          · have := (Option.some_injective _ h_eq_j0).symm; subst this
            simp only [pend_val, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
              decide_eq_false_iff_not, not_le] at hpend
            exact hpend.2
          · have := (Option.some_injective _ h_eq_j0).symm; subst this
            have h_in := seq_min_in_seq (FP_to_JLFP job_task higher_eq_priority) _ _ hp_val
            simp only [pending_jobs_other_than_j] at h_in
            rw [List.mem_filter] at h_in
            simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
              decide_eq_false_iff_not, not_le] at h_in
            exact h_in.2.1.2
      · simp only [Bool.not_eq_true] at hpend
        simp only [hpend, Bool.false_eq_true, ↓reduceIte] at h_eq_j0
        cases hp_val : hp with
        | none => simp [hp_val] at h_eq_j0
        | some j_hp =>
          simp only [hp_val] at h_eq_j0
          have := (Option.some_injective _ h_eq_j0).symm; subst this
          have h_in := seq_min_in_seq (FP_to_JLFP job_task higher_eq_priority) _ _ hp_val
          simp only [pending_jobs_other_than_j] at h_in
          rw [List.mem_filter] at h_in
          simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
            decide_eq_false_iff_not, not_le] at h_in
          exact h_in.2.1.2

include H_arrival_times_are_consistent in
theorem sched_jitter_work_conserving :
    work_conserving job_arrival
      (inflated_job_cost_local job_cost job_suspension_duration j)
      (job_jitter_local job_arrival job_task higher_eq_priority job_cost j R)
      arr_seq
      (sched_jitter_local job_arrival job_task arr_seq higher_eq_priority
        job_cost job_suspension_duration j R) := by
  intro j0 t IN BACK
  obtain ⟨PEND, NOTSCHED⟩ := BACK
  have USE := sched_jitter_uses_construction_function job_arrival job_task arr_seq higher_eq_priority
    job_cost job_suspension_duration j R t
  simp only [sched_jitter_local, build_schedule_local, inflated_job_cost_local, job_jitter_local] at USE PEND NOTSCHED ⊢
  set sched_j := sched_jitter job_arrival job_task higher_eq_priority job_cost job_suspension_duration arr_seq j R
  set jj := job_jitter job_arrival job_task higher_eq_priority job_cost j R
  -- We need to show ∃ j', scheduled_at sched_j j' t = true
  -- Since NOTSCHED says j0 is not scheduled, and PEND says j0 is pending,
  -- we show the schedule is non-empty by construction.
  -- The schedule at time t is: build_schedule sched_j t
  -- Key: if j is pending, schedule picks j or hp; if j not pending, schedule picks hp.
  -- We just need to show something is scheduled.
  suffices h : ∃ j', sched_j t = some j' by
    obtain ⟨j', hj'⟩ := h
    exact ⟨j', by simp only [scheduled_at]; rw [hj']; simp⟩
  rw [USE]
  simp only [build_schedule, highest_priority_job_other_than_j]
  set pend_j := (decide (actual_arrival job_arrival jj j ≤ t) &&
    !decide (inflated_job_cost job_cost job_suspension_duration j j ≤ service sched_j j t))
  set hp := seq_min (FP_to_JLFP job_task higher_eq_priority)
    (pending_jobs_other_than_j job_arrival job_task higher_eq_priority job_cost
      job_suspension_duration arr_seq j R sched_j t)
  by_cases hpend_j : pend_j = true
  · simp only [hpend_j, ↓reduceIte]
    cases hp_val : hp with
    | none => exact ⟨j, rfl⟩
    | some j_hp =>
      simp only
      split_ifs with hprio
      · exact ⟨j, rfl⟩
      · exact ⟨j_hp, rfl⟩
  · have hpf : pend_j = false := by cases h : pend_j <;> simp_all
    simp only [hpf, Bool.false_eq_true, ↓reduceIte]
    -- hp must be some because either j0 is pending and j0 ≠ j
    -- or j0 = j and j0 is pending → contradiction with hpf
    by_cases hj0j : j0 = j
    · subst hj0j
      -- j is pending, but pend_j = false. Contradiction.
      exfalso
      simp only [Prosa.Classic.Model.Schedule.Uni.Jitter.Schedule.pending] at PEND
      obtain ⟨PARR, PNCOMP⟩ := PEND
      simp only [pend_j] at hpf
      -- hpf : (decide (... ≤ t) && !decide (... ≤ service ...)) = false
      -- PARR : jitter_has_passed ... j0 t (i.e., actual_arrival ... ≤ t)
      -- PNCOMP : ¬completed_by ...  (i.e., ¬(... ≤ service ...))
      rw [Bool.and_eq_false_iff] at hpf
      cases hpf with
      | inl h =>
        rw [decide_eq_false_iff_not] at h
        exact absurd PARR h
      | inr h =>
        rw [Bool.not_eq_false'] at h
        rw [decide_eq_true_eq] at h
        exact PNCOMP h
    · -- j0 ≠ j, so j0 ∈ pending_jobs_other_than_j
      have h_in_pend : j0 ∈ pending_jobs_other_than_j job_arrival job_task higher_eq_priority
          job_cost job_suspension_duration arr_seq j R sched_j t := by
        simp only [pending_jobs_other_than_j]
        rw [List.mem_filter]
        simp only [Prosa.Classic.Model.Schedule.Uni.Jitter.Schedule.pending] at PEND
        obtain ⟨PARR, PNCOMP⟩ := PEND
        constructor
        · apply arrived_between_implies_in_actual_arrivals job_arrival jj arr_seq
            H_arrival_times_are_consistent j0 0 (t + 1) IN
          exact ⟨Nat.zero_le _, by simp only [jitter_has_passed, actual_arrival, Time] at PARR ⊢; omega⟩
        · simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
            decide_eq_false_iff_not, not_le]
          refine ⟨⟨PARR, ?_⟩, hj0j⟩
          simp only [completed_by] at PNCOMP
          exact Nat.lt_of_not_le PNCOMP
      have h_ne_none := seq_min_exists (FP_to_JLFP job_task higher_eq_priority)
        (pending_jobs_other_than_j job_arrival job_task higher_eq_priority job_cost
          job_suspension_duration arr_seq j R sched_j t) j0 h_in_pend
      cases hp_val : hp with
      | none => exfalso; exact h_ne_none hp_val
      | some j_hp => exact ⟨j_hp, rfl⟩

include H_arrival_times_are_consistent H_jobs_from_taskset H_priority_is_reflexive H_priority_is_transitive H_priority_is_total H_valid_schedule H_from_arrival_sequence in
theorem sched_jitter_respects_policy :
    respects_FP_policy job_arrival
      (inflated_job_cost_local job_cost job_suspension_duration j)
      (job_jitter_local job_arrival job_task higher_eq_priority job_cost j R)
      job_task arr_seq
      (sched_jitter_local job_arrival job_task arr_seq higher_eq_priority
        job_cost job_suspension_duration j R)
      higher_eq_priority := by
  -- j1 is backlogged, j2 is scheduled; we need higher_eq_priority (job_task j2) (job_task j1)
  intro j1 j2 t IN ⟨PEND, NOTSCHED⟩ SCHED
  have USE := sched_jitter_uses_construction_function job_arrival job_task arr_seq higher_eq_priority
    job_cost job_suspension_duration j R t
  simp only [sched_jitter_local, build_schedule_local, inflated_job_cost_local, job_jitter_local] at USE PEND NOTSCHED SCHED ⊢
  set sched_j := sched_jitter job_arrival job_task higher_eq_priority job_cost job_suspension_duration arr_seq j R
  set jj := job_jitter job_arrival job_task higher_eq_priority job_cost j R
  -- Determine j2 from SCHED
  simp only [scheduled_at] at SCHED
  rw [USE] at SCHED
  -- SCHED : (build_schedule ... sched_j t == some j2) = true
  -- Extract: build_schedule ... sched_j t = some j2
  have SCHED_EQ : build_schedule job_arrival job_task higher_eq_priority job_cost
      job_suspension_duration arr_seq j R sched_j t = some j2 := by
    exact beq_iff_eq.mp SCHED
  -- Helper: seq_min picks a job with highest priority over all pending_jobs_other_than_j
  set hp := seq_min (FP_to_JLFP job_task higher_eq_priority)
    (pending_jobs_other_than_j job_arrival job_task higher_eq_priority job_cost
      job_suspension_duration arr_seq j R sched_j t)
  have ALL : ∀ j_hi j_lo, hp = some j_hi →
      j_lo ∈ pending_jobs_other_than_j job_arrival job_task higher_eq_priority job_cost
        job_suspension_duration arr_seq j R sched_j t →
      higher_eq_priority (job_task j_hi) (job_task j_lo) = true := by
    intro j_hi j_lo SOME INlo
    apply seq_min_computes_min (FP_to_JLFP job_task higher_eq_priority)
      (fun x y z => H_priority_is_transitive (job_task y) (job_task x) (job_task z))
      (pending_jobs_other_than_j job_arrival job_task higher_eq_priority job_cost
        job_suspension_duration arr_seq j R sched_j t)
    · intro x y hx hy
      simp only [FP_to_JLFP]
      simp only [pending_jobs_other_than_j] at hx hy
      have hx_mem := List.mem_of_mem_filter hx
      have hy_mem := List.mem_of_mem_filter hy
      have hx_arr := in_actual_arrivals_between_implies_arrived job_arrival jj arr_seq
        H_arrival_times_are_consistent x 0 (t + 1) hx_mem
      have hy_arr := in_actual_arrivals_between_implies_arrived job_arrival jj arr_seq
        H_arrival_times_are_consistent y 0 (t + 1) hy_mem
      exact H_priority_is_total (job_task x) (job_task y) (H_jobs_from_taskset x hx_arr) (H_jobs_from_taskset y hy_arr)
    · exact SOME
    · exact INlo
  -- Helper: j1 ∈ pending_jobs_other_than_j when j1 ≠ j
  have j1_in_pend : j1 ≠ j → j1 ∈ pending_jobs_other_than_j job_arrival job_task higher_eq_priority
      job_cost job_suspension_duration arr_seq j R sched_j t := by
    intro hne
    simp only [pending_jobs_other_than_j]
    rw [List.mem_filter]
    obtain ⟨PARR, PNCOMP⟩ := PEND
    constructor
    · apply arrived_between_implies_in_actual_arrivals job_arrival jj arr_seq
        H_arrival_times_are_consistent j1 0 (t + 1) IN
      exact ⟨Nat.zero_le _, by simp only [jitter_has_passed, actual_arrival, Time] at PARR ⊢; omega⟩
    · simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
        decide_eq_false_iff_not, not_le]
      simp only [completed_by] at PNCOMP
      exact ⟨⟨PARR, Nat.lt_of_not_le PNCOMP⟩, hne⟩
  -- Analyze build_schedule to determine j2
  -- Use split_ifs and cases directly on SCHED_EQ, without set abbreviations
  simp only [build_schedule, highest_priority_job_other_than_j] at SCHED_EQ
  split_ifs at SCHED_EQ with hpend_j
  · -- pend_j = true (j is pending)
    -- SCHED_EQ has a match on seq_min
    generalize h_hp : seq_min (FP_to_JLFP job_task higher_eq_priority)
      (pending_jobs_other_than_j job_arrival job_task higher_eq_priority job_cost
        job_suspension_duration arr_seq j R sched_j t) = hp_opt at SCHED_EQ
    cases hp_opt with
    | none =>
      -- SCHED_EQ: some j = some j2, so j2 = j
      have h2j : j2 = j := (Option.some_injective _ SCHED_EQ).symm
      by_cases hj1j : j1 = j
      · rw [h2j, hj1j]; exact H_priority_is_reflexive (job_task j)
      · exfalso
        have h_in := j1_in_pend hj1j
        exact (seq_min_exists (FP_to_JLFP job_task higher_eq_priority) _ j1 h_in) h_hp
    | some j_hp =>
      simp only [] at SCHED_EQ
      split_ifs at SCHED_EQ with hprio
      · -- j_hp does NOT have hep over j, j2 = j
        have h2j : j2 = j := (Option.some_injective _ SCHED_EQ).symm
        by_cases hj1j : j1 = j
        · rw [h2j, hj1j]; exact H_priority_is_reflexive (job_task j)
        · -- j1 ≠ j, need higher_eq_priority (job_task j) (job_task j1)
          rw [h2j]
          have h_in := j1_in_pend hj1j
          have h_jhp_j1 := ALL j_hp j1 h_hp h_in
          -- j_hp doesn't have hep over j
          simp only [FP_to_JLFP, Bool.not_eq_true'] at hprio
          -- By totality, j has hep over j_hp
          have j_hp_in := seq_min_in_seq (FP_to_JLFP job_task higher_eq_priority) _ j_hp h_hp
          simp only [pending_jobs_other_than_j] at j_hp_in
          have j_hp_mem := List.mem_of_mem_filter j_hp_in
          have j_hp_arr := in_actual_arrivals_between_implies_arrived job_arrival jj arr_seq
            H_arrival_times_are_consistent j_hp 0 (t + 1) j_hp_mem
          have h_total := H_priority_is_total (job_task j) (job_task j_hp)
            (H_jobs_from_taskset j H_from_arrival_sequence) (H_jobs_from_taskset j_hp j_hp_arr)
          cases h_total with
          | inl h_j_hep_jhp =>
            exact H_priority_is_transitive (job_task j_hp) (job_task j) (job_task j1) h_j_hep_jhp h_jhp_j1
          | inr h_jhp_hep_j =>
            exfalso
            simp only [FP_to_JLFP, h_jhp_hep_j, Bool.not_true] at hprio
            exact Bool.noConfusion hprio
      · -- j_hp has hep over j, j2 = j_hp
        have h2hp : j2 = j_hp := (Option.some_injective _ SCHED_EQ).symm
        rw [h2hp]
        by_cases hj1j : j1 = j
        · subst hj1j
          -- Need: higher_eq_priority (job_task j_hp) (job_task j)
          simp only [FP_to_JLFP, Bool.not_eq_true'] at hprio
          -- hprio : higher_eq_priority ... ≠ false, need = true
          cases h : higher_eq_priority (job_task j_hp) (job_task j1) with
          | true => rfl
          | false => exact absurd h hprio
        · exact ALL j_hp j1 h_hp (j1_in_pend hj1j)
  · -- pend_j = false (j is NOT pending)
    -- SCHED_EQ: seq_min ... = some j2
    generalize h_hp : seq_min (FP_to_JLFP job_task higher_eq_priority)
      (pending_jobs_other_than_j job_arrival job_task higher_eq_priority job_cost
        job_suspension_duration arr_seq j R sched_j t) = hp_opt at SCHED_EQ
    cases hp_opt with
    | none => exact absurd SCHED_EQ (by simp)
    | some j_hp =>
      have h2hp : j2 = j_hp := (Option.some_injective _ SCHED_EQ).symm
      rw [h2hp]
      by_cases hj1j : j1 = j
      · subst hj1j
        -- j1 = j, but pend_j = false. But j is pending → contradiction
        exfalso
        obtain ⟨PARR, PNCOMP⟩ := PEND
        simp only [completed_by] at PNCOMP
        -- hpend_j is the negation of the boolean being true
        simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
          decide_eq_false_iff_not, not_le, not_and, not_not] at hpend_j
        exact PNCOMP (Nat.le_of_not_lt (hpend_j PARR))
      · exact ALL j_hp j1 h_hp (j1_in_pend hj1j)

include H_arrival_times_are_consistent H_jobs_from_taskset H_priority_is_reflexive H_priority_is_transitive H_priority_is_total H_valid_schedule H_from_arrival_sequence in
theorem sched_jitter_is_valid :
    valid_jitter_aware_schedule job_arrival arr_seq
      (job_higher_eq_priority job_task higher_eq_priority)
      (inflated_job_cost_local job_cost job_suspension_duration j)
      (job_jitter_local job_arrival job_task higher_eq_priority job_cost j R)
      (sched_jitter_local job_arrival job_task arr_seq higher_eq_priority
        job_cost job_suspension_duration j R) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact @sched_jitter_jobs_come_from_arrival_sequence _ _ _ _ job_arrival job_task arr_seq
      H_arrival_times_are_consistent higher_eq_priority job_cost job_suspension_duration
      j H_from_arrival_sequence R
  · exact sched_jitter_jobs_execute_after_jitter job_arrival job_task arr_seq
      higher_eq_priority job_cost job_suspension_duration j R
  · exact sched_jitter_completed_jobs_dont_execute job_arrival job_task arr_seq
      higher_eq_priority job_cost job_suspension_duration j R
  · exact @sched_jitter_work_conserving _ _ _ _ job_arrival job_task arr_seq
      H_arrival_times_are_consistent higher_eq_priority job_cost job_suspension_duration
      j R
  · intro j1 j_hp t hIN hBACK hSCHED
    exact @sched_jitter_respects_policy _ _ _ _ job_arrival job_task ts arr_seq
      H_arrival_times_are_consistent H_jobs_from_taskset higher_eq_priority
      H_priority_is_reflexive H_priority_is_transitive H_priority_is_total
      job_cost job_suspension_duration sched_susp H_valid_schedule
      j H_from_arrival_sequence R j1 j_hp t hIN hBACK hSCHED

include H_arrival_times_are_consistent H_jobs_from_taskset H_priority_is_reflexive H_priority_is_transitive H_priority_is_total H_valid_schedule H_from_arrival_sequence in
theorem sched_jitter_does_not_pick_j :
    ∀ j_hp t,
      arrives_in arr_seq j_hp →
      j_hp ≠ j →
      Prosa.Classic.Model.Schedule.Uni.Jitter.Schedule.pending job_arrival
        (inflated_job_cost_local job_cost job_suspension_duration j)
        (job_jitter_local job_arrival job_task higher_eq_priority job_cost j R)
        (sched_jitter_local job_arrival job_task arr_seq higher_eq_priority
          job_cost job_suspension_duration j R)
        j_hp t →
      higher_eq_priority (job_task j_hp) (job_task j) = true →
      ¬ (scheduled_at
        (sched_jitter_local job_arrival job_task arr_seq higher_eq_priority
          job_cost job_suspension_duration j R)
        j t = true) := by
  intro j_hp t ARRhp NEQ PENDhp HP SCHEDj
  have USE := sched_jitter_uses_construction_function job_arrival job_task arr_seq higher_eq_priority
    job_cost job_suspension_duration j R t
  simp only [sched_jitter_local, build_schedule_local, inflated_job_cost_local, job_jitter_local] at USE PENDhp SCHEDj
  set sched_j := sched_jitter job_arrival job_task higher_eq_priority job_cost job_suspension_duration arr_seq j R
  set jj := job_jitter job_arrival job_task higher_eq_priority job_cost j R
  simp only [scheduled_at] at SCHEDj
  rw [USE] at SCHEDj
  simp only [build_schedule, highest_priority_job_other_than_j] at SCHEDj
  set pend_val := (decide (actual_arrival job_arrival jj j ≤ t) &&
    !decide (inflated_job_cost job_cost job_suspension_duration j j ≤ service sched_j j t))
  set hp := seq_min (FP_to_JLFP job_task higher_eq_priority)
    (pending_jobs_other_than_j job_arrival job_task higher_eq_priority job_cost
      job_suspension_duration arr_seq j R sched_j t)
  -- j_hp is in pending_jobs_other_than_j
  have INhp : j_hp ∈ pending_jobs_other_than_j job_arrival job_task higher_eq_priority
      job_cost job_suspension_duration arr_seq j R sched_j t := by
    simp only [pending_jobs_other_than_j]
    rw [List.mem_filter]
    obtain ⟨PARRhp, PNCOMPhp⟩ := PENDhp
    constructor
    · apply arrived_between_implies_in_actual_arrivals job_arrival jj arr_seq
        H_arrival_times_are_consistent j_hp 0 (t + 1) ARRhp
      exact ⟨Nat.zero_le _, by simp only [jitter_has_passed, actual_arrival, Time] at PARRhp ⊢; omega⟩
    · simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
        decide_eq_false_iff_not, not_le]
      simp only [completed_by] at PNCOMPhp
      exact ⟨⟨PARRhp, Nat.lt_of_not_le PNCOMPhp⟩, NEQ⟩
  by_cases hpend : pend_val = true
  · simp only [hpend, ↓reduceIte] at SCHEDj
    cases hp_val : hp with
    | none =>
      -- hp = none but j_hp ∈ pending_jobs_other_than_j → contradiction
      exfalso
      exact (seq_min_exists (FP_to_JLFP job_task higher_eq_priority)
        (pending_jobs_other_than_j job_arrival job_task higher_eq_priority job_cost
          job_suspension_duration arr_seq j R sched_j t) j_hp INhp) hp_val
    | some j_hp' =>
      simp only [hp_val] at SCHEDj
      -- ALL: j_hp' has higher priority over all pending jobs other than j
      have TOTAL_PEND : ∀ x y : Job,
          x ∈ pending_jobs_other_than_j job_arrival job_task higher_eq_priority job_cost
            job_suspension_duration arr_seq j R sched_j t →
          y ∈ pending_jobs_other_than_j job_arrival job_task higher_eq_priority job_cost
            job_suspension_duration arr_seq j R sched_j t →
          FP_to_JLFP job_task higher_eq_priority x y = true ∨
          FP_to_JLFP job_task higher_eq_priority y x = true := by
        intro x y hx hy
        simp only [FP_to_JLFP]
        simp only [pending_jobs_other_than_j] at hx hy
        have hx_mem := List.mem_of_mem_filter hx
        have hy_mem := List.mem_of_mem_filter hy
        have hx_arr := in_actual_arrivals_between_implies_arrived job_arrival jj arr_seq
          H_arrival_times_are_consistent x 0 (t + 1) hx_mem
        have hy_arr := in_actual_arrivals_between_implies_arrived job_arrival jj arr_seq
          H_arrival_times_are_consistent y 0 (t + 1) hy_mem
        exact H_priority_is_total (job_task x) (job_task y) (H_jobs_from_taskset x hx_arr) (H_jobs_from_taskset y hy_arr)
      have ALL : ∀ j_lo, j_lo ∈ pending_jobs_other_than_j job_arrival job_task higher_eq_priority
          job_cost job_suspension_duration arr_seq j R sched_j t →
          higher_eq_priority (job_task j_hp') (job_task j_lo) = true := by
        intro j_lo INlo
        exact seq_min_computes_min (FP_to_JLFP job_task higher_eq_priority)
          (fun x y z => H_priority_is_transitive (job_task y) (job_task x) (job_task z))
          (pending_jobs_other_than_j job_arrival job_task higher_eq_priority job_cost
            job_suspension_duration arr_seq j R sched_j t) TOTAL_PEND j_hp' j_lo hp_val INlo
      split_ifs at SCHEDj with hprio
      · -- !(FP_to_JLFP ... j_hp' j) = true, i.e., j_hp' does NOT have hep over j
        -- But j_hp' hep j_hp (from ALL), and j_hp hep j (HP). By transitivity j_hp' hep j.
        -- This contradicts hprio.
        have h1 := ALL j_hp INhp
        have h2 := H_priority_is_transitive (job_task j_hp) (job_task j_hp') (job_task j) h1 HP
        simp only [FP_to_JLFP, h2] at hprio
        exact absurd hprio (by decide)
      · -- j_hp' is scheduled (SCHEDj says sched = some j_hp'), but SCHEDj should be sched = some j
        -- SCHEDj: (some j_hp' == some j) = true
        have h_eq := Option.some_injective _ (beq_iff_eq.mp SCHEDj)
        -- h_eq : j_hp' = j
        -- But j_hp' ∈ pending_jobs_other_than_j, which requires j_hp' ≠ j
        have j_hp'_in := seq_min_in_seq (FP_to_JLFP job_task higher_eq_priority)
          (pending_jobs_other_than_j job_arrival job_task higher_eq_priority job_cost
            job_suspension_duration arr_seq j R sched_j t) j_hp' hp_val
        simp only [pending_jobs_other_than_j] at j_hp'_in
        rw [List.mem_filter] at j_hp'_in
        simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
          decide_eq_false_iff_not, not_le] at j_hp'_in
        exact j_hp'_in.2.2 h_eq
  · -- pend_val = false
    have hpend_false : pend_val = false := by cases h : pend_val <;> simp_all
    simp only [hpend_false, Bool.false_eq_true, ↑reduceIte] at SCHEDj
    -- hp is the scheduled job, and SCHEDj says it equals j
    cases hp_val : hp with
    | none => simp [hp_val] at SCHEDj
    | some j_hp' =>
      simp only [hp_val] at SCHEDj
      have h_eq := Option.some_injective _ (beq_iff_eq.mp SCHEDj)
      -- h_eq : j_hp' = j
      -- But j_hp' ∈ pending_jobs_other_than_j requires j_hp' ≠ j → contradiction
      have j_hp'_in := seq_min_in_seq (FP_to_JLFP job_task higher_eq_priority)
        (pending_jobs_other_than_j job_arrival job_task higher_eq_priority job_cost
          job_suspension_duration arr_seq j R sched_j t) j_hp' hp_val
      simp only [pending_jobs_other_than_j] at j_hp'_in
      rw [List.mem_filter] at j_hp'_in
      simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
        decide_eq_false_iff_not, not_le] at j_hp'_in
      exact j_hp'_in.2.2 h_eq

end ScheduleIsValid

end ProvingScheduleProperties

end JitterScheduleProperties

end Prosa.Classic.Analysis.Uni.Susp.Dynamic.Jitter.Jitter_schedule_properties

end
