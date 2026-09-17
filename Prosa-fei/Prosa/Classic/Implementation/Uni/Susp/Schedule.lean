-- Translated from: classic/implementation/uni/susp/schedule.v
import Prosa.Classic.Util.All
import Prosa.Classic.Model.Arrival.Basic.Job
import Prosa.Classic.Model.Arrival.Basic.Arrival_sequence
import Prosa.Classic.Model.Priority
import Prosa.Classic.Model.Schedule.Uni.Schedule
import Prosa.Classic.Model.Schedule.Uni.Susp.Platform
import Prosa.Classic.Model.Schedule.Uni.Susp.Schedule
import Prosa.Classic.Model.Schedule.Uni.Susp.Suspension_intervals
import Prosa.Classic.Model.Schedule.Uni.Transformation.Construction
import Prosa.Classic.Model.Suspension
import Prosa.Classic.Util.Minmax
import Mathlib.Tactic

namespace Prosa.Classic.Implementation.Uni.Susp.Schedule

open Prosa.Classic.Model.Time
open Prosa.Classic.Model.Arrival.Basic.Job
open Prosa.Classic.Model.Arrival.Basic.Arrival_sequence
open Prosa.Classic.Model.Priority
open Prosa.Classic.Model.Schedule.Uni.Schedule
open Prosa.Classic.Model.Schedule.Uni.Susp.Platform.PlatformWithSuspensions
open Prosa.Classic.Model.Schedule.Uni.Susp.Schedule
open Prosa.Classic.Model.Schedule.Uni.Susp.Suspension_intervals
open Prosa.Classic.Model.Schedule.Uni.Susp.Last_execution
open Prosa.Classic.Model.Schedule.Uni.Transformation.Construction.ScheduleConstruction
open Prosa.Classic.Model.Suspension
open Prosa.Classic.Util.Minmax
open Classical

noncomputable section

namespace ConcreteScheduler

section Implementation

variable {Job : Type _} [DecidableEq Job]
variable (job_arrival : Job → Time)
variable (job_cost : Job → Time)
variable (arr_seq : arrival_sequence Job)
variable (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq)
variable (next_suspension : job_suspension Job)
variable (higher_eq_priority : JLDP_policy Job)

section ScheduleConstruction

variable (sched_prefix : schedule Job)
variable (t : Time)

def pending_jobs : List Job :=
  (jobs_arrived_up_to arr_seq t).filter
    (fun j => pending job_arrival job_cost sched_prefix j t ∧
              ¬ suspended_at job_arrival job_cost next_suspension sched_prefix j t)

def highest_priority_job : Option Job :=
  seq_min (higher_eq_priority t)
    (pending_jobs job_arrival job_cost arr_seq next_suspension sched_prefix t)

end ScheduleConstruction

private def empty_schedule : schedule Job := fun _ => none

def scheduler : schedule Job :=
  build_schedule_from_prefixes
    (fun sched_prefix t =>
      highest_priority_job job_arrival job_cost arr_seq next_suspension higher_eq_priority sched_prefix t)
    empty_schedule

omit H_arrival_times_are_consistent in
theorem scheduler_depends_only_on_prefix :
    ∀ (sched1 sched2 : schedule Job) (t : Time),
      (∀ t0, t0 < t → sched1 t0 = sched2 t0) →
      highest_priority_job job_arrival job_cost arr_seq next_suspension higher_eq_priority sched1 t =
      highest_priority_job job_arrival job_cost arr_seq next_suspension higher_eq_priority sched2 t := by
  intro sched1 sched2 t ALL
  simp only [highest_priority_job]
  suffices h_same : pending_jobs job_arrival job_cost arr_seq next_suspension sched1 t =
      pending_jobs job_arrival job_cost arr_seq next_suspension sched2 t by
    rw [h_same]
  simp only [pending_jobs]
  congr 1
  ext j
  simp only [decide_eq_decide]
  -- Helper: scheduled_at is the same for all times < t
  have h_sched_at_eq : ∀ t0 < t, scheduled_at sched1 j t0 = scheduled_at sched2 j t0 := by
    intro t0 ht0; simp only [scheduled_at]; rw [ALL t0 ht0]
  -- Service depends only on prefix
  have h_serv_eq : ∀ t' : Time, t' ≤ t → service sched1 j t' = service sched2 j t' := by
    intro t' ht'
    simp only [service, service_during]
    apply Finset.sum_congr rfl
    intro i hi; rw [Finset.mem_Ico] at hi
    simp only [service_at, h_sched_at_eq i (Nat.lt_of_lt_of_le hi.2 ht')]
  -- scheduled_before depends only on prefix
  have h_sched_before : scheduled_before sched1 j t = scheduled_before sched2 j t := by
    unfold scheduled_before
    congr 1; apply propext
    constructor
    · intro ⟨⟨v, hlt⟩, h⟩; exact ⟨⟨v, hlt⟩, by rw [← h_sched_at_eq v hlt]; exact h⟩
    · intro ⟨⟨v, hlt⟩, h⟩; exact ⟨⟨v, hlt⟩, by rw [h_sched_at_eq v hlt]; exact h⟩
  -- last_time_scheduled depends only on prefix
  have h_last_sched : last_time_scheduled sched1 j t = last_time_scheduled sched2 j t := by
    unfold last_time_scheduled
    congr 1; unfold max_nat_cond; congr 1
    apply List.filter_congr
    intro t0 ht0
    have ht0_lt : t0 < t := by
      rw [mem_values_between] at ht0; exact ht0.2
    exact h_sched_at_eq t0 ht0_lt
  -- time_after_last_execution depends only on prefix
  have h_last : time_after_last_execution job_arrival sched1 j t =
      time_after_last_execution job_arrival sched2 j t := by
    unfold time_after_last_execution
    rw [h_sched_before, h_last_sched]
  -- suspended_at equality (case split on time_after_last_execution ≤ t)
  have h_susp_eq : suspended_at job_arrival job_cost next_suspension sched1 j t =
      suspended_at job_arrival job_cost next_suspension sched2 j t := by
    simp only [suspended_at, suspension_duration, completed_by, h_serv_eq t le_rfl, h_last]
    by_cases h_le : time_after_last_execution job_arrival sched2 j t ≤ t
    · simp only [h_serv_eq _ h_le]
    · apply propext
      exact ⟨fun ⟨_, h, _⟩ => absurd h h_le, fun ⟨_, h, _⟩ => absurd h h_le⟩
  -- pending equality
  have h_pend_eq : pending job_arrival job_cost sched1 j t =
      pending job_arrival job_cost sched2 j t := by
    simp only [pending, completed_by, h_serv_eq t le_rfl]
  simp only [h_pend_eq, h_susp_eq]

omit H_arrival_times_are_consistent in
theorem scheduler_uses_construction_function :
    ∀ t,
      scheduler job_arrival job_cost arr_seq next_suspension higher_eq_priority t =
      highest_priority_job job_arrival job_cost arr_seq next_suspension higher_eq_priority
        (scheduler job_arrival job_cost arr_seq next_suspension higher_eq_priority) t := by
  intro t
  exact prefix_dependent_schedule_construction
    (fun sched_prefix t =>
      highest_priority_job job_arrival job_cost arr_seq next_suspension higher_eq_priority sched_prefix t)
    empty_schedule
    (scheduler_depends_only_on_prefix job_arrival job_cost arr_seq
      next_suspension higher_eq_priority)
    t

end Implementation

section Proofs

variable {Job : Type _} [DecidableEq Job]
variable (job_arrival : Job → Time)
variable (job_cost : Job → Time)
variable (arr_seq : arrival_sequence Job)
variable (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq)
variable (H_no_duplicate_arrivals : arrival_sequence_is_a_set arr_seq)
variable (next_suspension : job_suspension Job)
variable (higher_eq_priority : JLDP_policy Job)
variable (H_priority_is_transitive : JLDP_is_transitive higher_eq_priority)
variable (H_priority_is_total : JLDP_is_total arr_seq higher_eq_priority)

private theorem scheduled_in_pending_jobs (j : Job) (t : Time) :
    scheduled_at (scheduler job_arrival job_cost arr_seq next_suspension higher_eq_priority) j t = true →
    j ∈ pending_jobs job_arrival job_cost arr_seq next_suspension
      (scheduler job_arrival job_cost arr_seq next_suspension higher_eq_priority) t := by
  intro SCHED
  simp only [scheduled_at] at SCHED
  have h_eq := scheduler_uses_construction_function job_arrival job_cost arr_seq
    next_suspension higher_eq_priority t
  rw [h_eq] at SCHED
  simp only [highest_priority_job] at SCHED
  exact seq_min_in_seq _ _ j (by rw [beq_iff_eq] at SCHED; exact SCHED)

include H_arrival_times_are_consistent in
omit H_no_duplicate_arrivals H_priority_is_transitive H_priority_is_total in
theorem scheduler_jobs_come_from_arrival_sequence :
    jobs_come_from_arrival_sequence
      (scheduler job_arrival job_cost arr_seq next_suspension higher_eq_priority)
      arr_seq := by
  intro j t SCHED
  have h_mem := scheduled_in_pending_jobs job_arrival job_cost arr_seq
    next_suspension higher_eq_priority j t SCHED
  simp only [pending_jobs, List.mem_filter, decide_eq_true_eq] at h_mem
  exact in_arrivals_implies_arrived job_arrival arr_seq H_arrival_times_are_consistent j 0 (t + 1) h_mem.1

omit H_no_duplicate_arrivals H_priority_is_transitive H_priority_is_total H_arrival_times_are_consistent in
theorem scheduler_jobs_must_arrive_to_execute :
    jobs_must_arrive_to_execute job_arrival
      (scheduler job_arrival job_cost arr_seq next_suspension higher_eq_priority) := by
  intro j t SCHED
  have h_mem := scheduled_in_pending_jobs job_arrival job_cost arr_seq
    next_suspension higher_eq_priority j t SCHED
  simp only [pending_jobs, List.mem_filter, decide_eq_true_eq] at h_mem
  exact h_mem.2.1.1

omit H_no_duplicate_arrivals H_priority_is_transitive H_priority_is_total in
theorem scheduler_completed_jobs_dont_execute :
    completed_jobs_dont_execute job_cost
      (scheduler job_arrival job_cost arr_seq next_suspension higher_eq_priority) := by
  intro j t
  induction t with
  | zero =>
    simp only [service, service_during, Finset.Ico_self, Finset.sum_empty]
    omega
  | succ n ih =>
    set sched := scheduler job_arrival job_cost arr_seq next_suspension higher_eq_priority with hsched_def
    suffices h : service sched j n + service_at sched j n ≤ job_cost j by
      simp only [service, service_during] at h ⊢
      rwa [Finset.sum_Ico_succ_top (Nat.zero_le n)]
    by_cases h : job_cost j ≤ service sched j n
    · have h_service_at_zero : service_at sched j n = 0 := by
        simp only [service_at, scheduled_at]
        cases hd : (sched n == some j)
        · simp [Bool.toNat]
        · exfalso
          have heq : sched n = some j := by rwa [beq_iff_eq] at hd
          rw [hsched_def] at heq
          rw [scheduler_uses_construction_function job_arrival job_cost arr_seq
            next_suspension higher_eq_priority] at heq
          have HIN := seq_min_in_seq (higher_eq_priority n)
            (pending_jobs job_arrival job_cost arr_seq next_suspension sched n) j heq
          simp only [pending_jobs, List.mem_filter, decide_eq_true_eq] at HIN
          exact HIN.2.1.2 h
      omega
    · -- service at n < cost, service_at ≤ 1
      have hle : service_at sched j n ≤ 1 := service_at_most_one _ j n
      simp only [Nat.not_le] at h; omega

include H_arrival_times_are_consistent in
omit H_no_duplicate_arrivals H_priority_is_transitive H_priority_is_total in
theorem scheduler_work_conserving :
    work_conserving job_arrival job_cost next_suspension arr_seq
      (scheduler job_arrival job_cost arr_seq next_suspension higher_eq_priority) := by
  intro j t h_arr h_back
  obtain ⟨⟨h_arrived, h_not_comp⟩, h_not_sched, h_not_susp⟩ := h_back
  -- Show j is in pending_jobs
  have h_j_in : j ∈ pending_jobs job_arrival job_cost arr_seq next_suspension
      (scheduler job_arrival job_cost arr_seq next_suspension higher_eq_priority) t := by
    simp only [pending_jobs, List.mem_filter, decide_eq_true_eq, jobs_arrived_up_to]
    exact ⟨arrived_between_implies_in_arrivals job_arrival arr_seq H_arrival_times_are_consistent
      j 0 (t + 1) h_arr ⟨Nat.zero_le _, by simp only [has_arrived] at h_arrived; simp only [Time] at *; omega⟩,
      ⟨h_arrived, h_not_comp⟩, h_not_susp⟩
  -- seq_min on non-empty list returns some value
  have h_ne := seq_min_exists (higher_eq_priority t)
    (pending_jobs job_arrival job_cost arr_seq next_suspension
      (scheduler job_arrival job_cost arr_seq next_suspension higher_eq_priority) t) j h_j_in
  -- Case split on highest_priority_job
  have hscf := scheduler_uses_construction_function job_arrival job_cost arr_seq
    next_suspension higher_eq_priority t
  cases HP : highest_priority_job job_arrival job_cost arr_seq next_suspension higher_eq_priority
      (scheduler job_arrival job_cost arr_seq next_suspension higher_eq_priority) t with
  | some j_hp =>
    exact ⟨j_hp, by simp only [scheduled_at]; rw [hscf, HP]; simp⟩
  | none =>
    exfalso
    simp only [highest_priority_job] at HP
    exact h_ne HP

include H_arrival_times_are_consistent H_priority_is_transitive H_priority_is_total in
omit H_no_duplicate_arrivals in
theorem scheduler_respects_policy :
    respects_JLDP_policy job_arrival job_cost next_suspension arr_seq
      (scheduler job_arrival job_cost arr_seq next_suspension higher_eq_priority)
      higher_eq_priority := by
  intro j1 j2 t h_arr1 h_back h_sched2
  obtain ⟨⟨h_arrived, h_not_comp⟩, h_not_sched, h_not_susp⟩ := h_back
  -- Get SCHED as an equation
  simp only [scheduled_at] at h_sched2
  have SCHED' : scheduler job_arrival job_cost arr_seq next_suspension higher_eq_priority t = some j2 := by
    rwa [beq_iff_eq] at h_sched2
  rw [scheduler_uses_construction_function job_arrival job_cost arr_seq
    next_suspension higher_eq_priority] at SCHED'
  simp only [highest_priority_job] at SCHED'
  -- j1 is in pending_jobs
  have h_j1_in : j1 ∈ pending_jobs job_arrival job_cost arr_seq next_suspension
      (scheduler job_arrival job_cost arr_seq next_suspension higher_eq_priority) t := by
    simp only [pending_jobs, List.mem_filter, decide_eq_true_eq, jobs_arrived_up_to]
    exact ⟨arrived_between_implies_in_arrivals job_arrival arr_seq H_arrival_times_are_consistent
      j1 0 (t + 1) h_arr1 ⟨Nat.zero_le _, by simp only [has_arrived] at h_arrived; simp only [Time] at *; omega⟩,
      ⟨h_arrived, h_not_comp⟩, h_not_susp⟩
  -- Use seq_min_computes_min
  exact seq_min_computes_min (higher_eq_priority t)
    (fun x y z hxy hyz => H_priority_is_transitive t y x z hxy hyz)
    (pending_jobs job_arrival job_cost arr_seq next_suspension
      (scheduler job_arrival job_cost arr_seq next_suspension higher_eq_priority) t)
    (fun x y hx hy => by
      simp only [pending_jobs, List.mem_filter, decide_eq_true_eq] at hx hy
      exact H_priority_is_total x y t
        (in_arrivals_implies_arrived job_arrival arr_seq H_arrival_times_are_consistent x 0 (t + 1) hx.1)
        (in_arrivals_implies_arrived job_arrival arr_seq H_arrival_times_are_consistent y 0 (t + 1) hy.1))
    j2 j1 SCHED' h_j1_in

omit H_no_duplicate_arrivals H_priority_is_transitive H_priority_is_total H_arrival_times_are_consistent in
theorem scheduler_respects_self_suspensions :
    respects_self_suspensions job_arrival job_cost next_suspension
      (scheduler job_arrival job_cost arr_seq next_suspension higher_eq_priority) := by
  intro j t SCHED
  have h_mem := scheduled_in_pending_jobs job_arrival job_cost arr_seq
    next_suspension higher_eq_priority j t SCHED
  simp only [pending_jobs, List.mem_filter, decide_eq_true_eq] at h_mem
  exact h_mem.2.2

end Proofs

end ConcreteScheduler

end

end Prosa.Classic.Implementation.Uni.Susp.Schedule
