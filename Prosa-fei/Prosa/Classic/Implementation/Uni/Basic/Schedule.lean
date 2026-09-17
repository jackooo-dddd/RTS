-- Translated from: ../rt-proofs/classic/implementation/uni/basic/schedule.v
import Prosa.Classic.Util.All
import Prosa.Classic.Model.Arrival.Basic.Job
import Prosa.Classic.Model.Schedule.Uni.Schedule
import Prosa.Classic.Model.Schedule.Uni.Basic.Platform
import Prosa.Classic.Model.Schedule.Uni.Transformation.Construction
import Prosa.Classic.Model.Arrival.Basic.Arrival_sequence
import Prosa.Classic.Model.Priority

namespace Prosa.Classic.Implementation.Uni.Basic.Schedule

open Prosa.Classic.Model.Time
open Prosa.Classic.Model.Arrival.Basic.Arrival_sequence
open Prosa.Classic.Model.Schedule.Uni.Schedule
open Prosa.Classic.Model.Schedule.Uni.Basic.Platform.Platform
open Prosa.Classic.Model.Schedule.Uni.Transformation.Construction.ScheduleConstruction
open Prosa.Classic.Model.Priority
open Prosa.Classic.Util.Minmax

namespace ConcreteScheduler

section Implementation

variable {Job : Type _} [DecidableEq Job]
variable (job_arrival : Job → Time)
variable (job_cost : Job → Time)
variable (arr_seq : arrival_sequence Job)
variable (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq)
variable (higher_eq_priority : JLDP_policy Job)

section ScheduleConstruction

variable (sched_prefix : schedule Job)
variable (t : Time)

def pending_jobs : List Job :=
  (jobs_arrived_up_to arr_seq t).filter
    (fun j => (decide (job_arrival j ≤ t)) && !(decide (job_cost j ≤ service sched_prefix j t)))

def highest_priority_job : Option Job :=
  seq_min (higher_eq_priority t) (pending_jobs job_arrival job_cost arr_seq sched_prefix t)

end ScheduleConstruction

private def empty_schedule : schedule Job := fun _ => none

def scheduler : schedule Job :=
  build_schedule_from_prefixes (highest_priority_job job_arrival job_cost arr_seq higher_eq_priority) (empty_schedule)

include H_arrival_times_are_consistent

theorem scheduler_depends_only_on_prefix :
    ∀ sched1 sched2 t,
      (∀ t0, t0 < t → sched1 t0 = sched2 t0) →
      highest_priority_job job_arrival job_cost arr_seq higher_eq_priority sched1 t =
      highest_priority_job job_arrival job_cost arr_seq higher_eq_priority sched2 t := by
  intro sched1 sched2 t ALL
  simp only [highest_priority_job]
  have SAME : pending_jobs job_arrival job_cost arr_seq sched1 t = pending_jobs job_arrival job_cost arr_seq sched2 t := by
    simp only [pending_jobs]
    congr 1
    ext j
    have hsvc : service sched1 j t = service sched2 j t := by
      simp only [service, service_during]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mem_Ico] at hi
      simp only [service_at, scheduled_at]
      rw [ALL i hi.2]
    rw [hsvc]
  rw [SAME]

theorem scheduler_uses_construction_function :
    ∀ t, scheduler job_arrival job_cost arr_seq higher_eq_priority t =
      highest_priority_job job_arrival job_cost arr_seq higher_eq_priority
        (scheduler job_arrival job_cost arr_seq higher_eq_priority) t := by
  intro t
  exact prefix_dependent_schedule_construction
    (highest_priority_job job_arrival job_cost arr_seq higher_eq_priority)
    (empty_schedule)
    (scheduler_depends_only_on_prefix job_arrival job_cost arr_seq H_arrival_times_are_consistent higher_eq_priority)
    t

end Implementation

section Proofs

variable {Job : Type _} [DecidableEq Job]
variable (job_arrival : Job → Time)
variable (job_cost : Job → Time)
variable (arr_seq : arrival_sequence Job)
variable (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq)
variable (H_arrival_sequence_is_a_set : arrival_sequence_is_a_set arr_seq)
variable (higher_eq_priority : JLDP_policy Job)
variable (H_priority_is_transitive : ∀ t, ∀ y x z, higher_eq_priority t x y = true → higher_eq_priority t y z = true → higher_eq_priority t x z = true)
variable (H_priority_is_total : ∀ t x y, higher_eq_priority t x y = true ∨ higher_eq_priority t y x = true)

include H_arrival_times_are_consistent H_arrival_sequence_is_a_set H_priority_is_transitive H_priority_is_total

theorem scheduler_jobs_come_from_arrival_sequence :
    jobs_come_from_arrival_sequence (scheduler job_arrival job_cost arr_seq higher_eq_priority) arr_seq := by
  intro j t SCHED
  simp only [scheduled_at] at SCHED
  have SCHED' : scheduler job_arrival job_cost arr_seq higher_eq_priority t = some j := by
    rwa [beq_iff_eq] at SCHED
  rw [scheduler_uses_construction_function job_arrival job_cost arr_seq H_arrival_times_are_consistent higher_eq_priority] at SCHED'
  have HIN := seq_min_in_seq (higher_eq_priority t)
    (pending_jobs job_arrival job_cost arr_seq (scheduler job_arrival job_cost arr_seq higher_eq_priority) t) j SCHED'
  simp only [pending_jobs] at HIN
  rw [List.mem_filter] at HIN
  exact in_arrivals_implies_arrived job_arrival arr_seq H_arrival_times_are_consistent j 0 (t + 1) HIN.1

theorem scheduler_jobs_must_arrive_to_execute :
    jobs_must_arrive_to_execute job_arrival (scheduler job_arrival job_cost arr_seq higher_eq_priority) := by
  intro j t SCHED
  simp only [scheduled_at] at SCHED
  have SCHED' : scheduler job_arrival job_cost arr_seq higher_eq_priority t = some j := by
    rwa [beq_iff_eq] at SCHED
  rw [scheduler_uses_construction_function job_arrival job_cost arr_seq H_arrival_times_are_consistent higher_eq_priority] at SCHED'
  have HIN := seq_min_in_seq (higher_eq_priority t)
    (pending_jobs job_arrival job_cost arr_seq (scheduler job_arrival job_cost arr_seq higher_eq_priority) t) j SCHED'
  simp only [pending_jobs] at HIN
  rw [List.mem_filter] at HIN
  obtain ⟨_, hcond⟩ := HIN
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_eq_eq_not, Bool.not_true] at hcond
  exact hcond.1

theorem scheduler_completed_jobs_dont_execute :
    completed_jobs_dont_execute job_cost (scheduler job_arrival job_cost arr_seq higher_eq_priority) := by
  intro j t
  induction t with
  | zero =>
    simp only [service, service_during, Finset.Ico_self, Finset.sum_empty]
    omega
  | succ n ih =>
    set sched := scheduler job_arrival job_cost arr_seq higher_eq_priority with hsched_def
    -- Unfold service to a sum so we can split off the last term
    suffices h : service sched j n + service_at sched j n ≤ job_cost j by
      simp only [service, service_during] at h ⊢
      rwa [Finset.sum_Ico_succ_top (Nat.zero_le n)]
    by_cases h : job_cost j ≤ service sched j n
    · -- service at n already ≥ cost, so service_at at n must be 0
      have h_service_at_zero : service_at sched j n = 0 := by
        simp only [service_at, scheduled_at]
        cases hd : (sched n == some j)
        · simp [Bool.toNat]
        · exfalso
          have heq : sched n = some j := by rwa [beq_iff_eq] at hd
          rw [hsched_def] at heq
          rw [scheduler_uses_construction_function job_arrival job_cost arr_seq H_arrival_times_are_consistent higher_eq_priority] at heq
          have HIN := seq_min_in_seq (higher_eq_priority n)
            (pending_jobs job_arrival job_cost arr_seq sched n) j heq
          simp only [pending_jobs] at HIN
          rw [List.mem_filter] at HIN
          obtain ⟨_, hcond⟩ := HIN
          simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at hcond
          exact hcond.2 h
      omega
    · -- service at n < cost
      push_neg at h
      have hle : service_at sched j n ≤ 1 := service_at_most_one _ j n
      have hlt : service sched j n + 1 ≤ job_cost j := h
      linarith

theorem scheduler_work_conserving :
    work_conserving job_arrival job_cost arr_seq (scheduler job_arrival job_cost arr_seq higher_eq_priority) := by
  intro j t IN BACK
  obtain ⟨⟨ARR, NOTCOMP⟩, NOTSCHED⟩ := BACK
  -- Show the pending_jobs list contains j
  have hj_in_pending : j ∈ pending_jobs job_arrival job_cost arr_seq (scheduler job_arrival job_cost arr_seq higher_eq_priority) t := by
    simp only [pending_jobs]
    rw [List.mem_filter]
    constructor
    · simp only [jobs_arrived_up_to]
      exact arrived_between_implies_in_arrivals job_arrival arr_seq H_arrival_times_are_consistent j 0 (t + 1) IN
        ⟨Nat.zero_le _, by simp only [has_arrived] at ARR; simp only [Time] at *; omega⟩
    · simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not]
      exact ⟨ARR, NOTCOMP⟩
  -- So seq_min returns some value
  have hne := seq_min_exists (higher_eq_priority t)
    (pending_jobs job_arrival job_cost arr_seq (scheduler job_arrival job_cost arr_seq higher_eq_priority) t) j hj_in_pending
  -- Look at what highest_priority_job returns
  have hscf := scheduler_uses_construction_function job_arrival job_cost arr_seq H_arrival_times_are_consistent higher_eq_priority t
  cases HP : highest_priority_job job_arrival job_cost arr_seq higher_eq_priority (scheduler job_arrival job_cost arr_seq higher_eq_priority) t with
  | some j_hp =>
    exact ⟨j_hp, by simp only [scheduled_at]; rw [hscf, HP]; simp⟩
  | none =>
    exfalso
    simp only [highest_priority_job] at HP
    exact hne HP

theorem scheduler_respects_policy :
    respects_JLDP_policy job_arrival job_cost arr_seq (scheduler job_arrival job_cost arr_seq higher_eq_priority) higher_eq_priority := by
  intro j1 j2 t ARR1 BACK SCHED
  obtain ⟨⟨ARR, NOTCOMP⟩, NOTSCHED⟩ := BACK
  -- Get SCHED as an equation on the schedule function
  simp only [scheduled_at] at SCHED
  have SCHED' : scheduler job_arrival job_cost arr_seq higher_eq_priority t = some j2 := by
    rwa [beq_iff_eq] at SCHED
  rw [scheduler_uses_construction_function job_arrival job_cost arr_seq H_arrival_times_are_consistent higher_eq_priority] at SCHED'
  simp only [highest_priority_job] at SCHED'
  -- j1 is in pending_jobs
  have hj1_in : j1 ∈ pending_jobs job_arrival job_cost arr_seq (scheduler job_arrival job_cost arr_seq higher_eq_priority) t := by
    simp only [pending_jobs]
    rw [List.mem_filter]
    constructor
    · simp only [jobs_arrived_up_to]
      exact arrived_between_implies_in_arrivals job_arrival arr_seq H_arrival_times_are_consistent j1 0 (t + 1) ARR1
        ⟨Nat.zero_le _, by simp only [has_arrived] at ARR; simp only [Time] at *; omega⟩
    · simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not]
      exact ⟨ARR, NOTCOMP⟩
  -- Use seq_min_computes_min
  exact seq_min_computes_min (higher_eq_priority t)
    (fun x y z hxy hyz => H_priority_is_transitive t y x z hxy hyz)
    (pending_jobs job_arrival job_cost arr_seq (scheduler job_arrival job_cost arr_seq higher_eq_priority) t)
    (fun x y _ _ => H_priority_is_total t x y)
    j2 j1 SCHED' hj1_in

end Proofs

end ConcreteScheduler

end Prosa.Classic.Implementation.Uni.Basic.Schedule
