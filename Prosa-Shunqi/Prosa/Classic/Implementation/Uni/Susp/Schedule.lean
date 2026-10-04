-- Authoritative source:
-- ProsaBuddy classic Prosa (prosabuddy commit f692cb7479780cf6009493f373a309e13165201c)
-- source: classic/implementation/uni/susp/schedule.v
-- sha256: see Prosa-Shunqi/classic-prosa/comprehensive-classic/file_order.csv (rank 137)

import Prosa.Classic.Util.All
import Prosa.Classic.Model.Arrival.Basic.Job
import Prosa.Classic.Model.Arrival.Basic.ArrivalSequence
import Prosa.Classic.Model.Priority
import Prosa.Classic.Model.Schedule.Uni.Schedule
import Prosa.Classic.Model.Schedule.Uni.Susp.Platform
import Prosa.Classic.Model.Schedule.Uni.Transformation.Construction

/-!
A concrete priority-based uniprocessor scheduler for self-suspending jobs (Rocq module `ConcreteScheduler` of
`classic/implementation/uni/susp/schedule.v`).

Representation notes:
* `[seq j <- s | P j]` is `s.filter P`; `~~ b` is `!b`; `seq_min` is the classic `Prosa.Classic.Util.Minmax.seq_min`.
* The section-local `Let`s (`is_pending`, `is_suspended`, `empty_schedule`, `sched`) are unfolded.
* Binder lists follow the Rocq contract.
-/

set_option linter.unusedVariables false

namespace Prosa.Classic.Implementation.Uni.Susp.Schedule.ConcreteScheduler

open Prosa.Classic.Model.Time.Time
open Prosa.Classic.Model.Arrival.Basic.ArrivalSequence.ArrivalSequence
open Prosa.Classic.Model.Priority.Priority
open Prosa.Classic.Model.Suspension.Suspension
open Prosa.Classic.Model.Schedule.Uni.Schedule.UniprocessorSchedule
open Prosa.Classic.Model.Schedule.Uni.Susp.LastExecution.LastExecution
open Prosa.Classic.Model.Schedule.Uni.Susp.SuspensionIntervals.SuspensionIntervals
open Prosa.Classic.Model.Schedule.Uni.Susp.Platform.PlatformWithSuspensions
open Prosa.Classic.Model.Schedule.Uni.Transformation.Construction.ScheduleConstruction
open Prosa.Classic.Util.Minmax (seq_min seq_min_in_seq seq_min_exists seq_min_computes_min)

universe v

local macro "omega'" : tactic =>
  `(tactic| ((try dsimp only [Prosa.Classic.Model.Time.Time.time,
    Prosa.Classic.Model.Time.Time.instant, Prosa.Classic.Model.Time.Time.duration] at *) <;>
    omega))

/-! ### Implementation -/

def pending_jobs {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time) (arr_seq : arrival_sequence Job)
    (next_suspension : job_suspension Job) (sched_prefix : schedule Job) (t : time) : List Job :=
  (jobs_arrived_up_to arr_seq t).filter (fun j =>
    pending job_arrival job_cost sched_prefix j t && !suspended_at job_arrival job_cost next_suspension sched_prefix j t)

def highest_priority_job {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time) (arr_seq : arrival_sequence Job)
    (next_suspension : job_suspension Job) (higher_eq_priority : JLDP_policy Job) (sched_prefix : schedule Job)
    (t : time) : Option Job :=
  seq_min (higher_eq_priority t) (pending_jobs job_arrival job_cost arr_seq next_suspension sched_prefix t)

def scheduler {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time) (arr_seq : arrival_sequence Job)
    (next_suspension : job_suspension Job) (higher_eq_priority : JLDP_policy Job) : schedule Job :=
  build_schedule_from_prefixes (highest_priority_job job_arrival job_cost arr_seq next_suspension higher_eq_priority) (fun _ => none)

/-- LEAN_HELPER: service up to `m` only depends on the schedule before `m`. -/
private theorem service_congr {Job : Type v} [DecidableEq Job] (s1 s2 : schedule Job) (x : Job) (m : time)
    (H : ∀ i, i < m → scheduled_at s1 x i = scheduled_at s2 x i) : service s1 x m = service s2 x m := by
  unfold service service_during
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_Ico] at hi
  simp only [service_at, H i hi.2]

/-- LEAN_HELPER: the time after the last execution before `k` only depends on the schedule before `k`. -/
private theorem tale_congr {Job : Type v} [DecidableEq Job] (job_arrival : Job → time) (s1 s2 : schedule Job) (x : Job) (k : time)
    (H : ∀ i, i < k → scheduled_at s1 x i = scheduled_at s2 x i) :
    time_after_last_execution job_arrival s1 x k = time_after_last_execution job_arrival s2 x k := by
  have F : (fun t0 : Fin k => scheduled_at s1 x t0) = (fun t0 : Fin k => scheduled_at s2 x t0) :=
    funext fun t0 => H t0 t0.isLt
  unfold time_after_last_execution
  simp only [F]

theorem scheduler_depends_only_on_prefix {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time) (arr_seq : arrival_sequence Job)
    (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq)
    (next_suspension : job_suspension Job) (higher_eq_priority : JLDP_policy Job) :
    ∀ (sched1 sched2 : schedule Job) (t : Nat), (∀ t0, t0 < t → sched1 t0 = sched2 t0) →
      highest_priority_job job_arrival job_cost arr_seq next_suspension higher_eq_priority sched1 t = highest_priority_job job_arrival job_cost arr_seq next_suspension higher_eq_priority sched2 t := by
  intro sched1 sched2 t ALL
  have SCH : ∀ x i, i < t → scheduled_at sched1 x i = scheduled_at sched2 x i := by
    intro x i hi; simp only [scheduled_at, ALL i hi]
  unfold highest_priority_job pending_jobs
  congr 1
  apply List.filter_congr
  intro j IN
  have ARRb := in_arrivals_implies_arrived_before job_arrival arr_seq H_arrival_times_are_consistent j (t + 1) IN
  have ARR : has_arrived job_arrival j t = true := by
    simp only [arrived_before, has_arrived, decide_eq_true_eq] at ARRb ⊢; omega'
  have COMP : completed_by job_cost sched1 j t = completed_by job_cost sched2 j t := by
    simp only [completed_by, service_congr sched1 sched2 j t (SCH j)]
  have TALE := tale_congr job_arrival sched1 sched2 j t (SCH j)
  have LE := last_execution_bounded_by_identity job_arrival sched2 j t ARR
  have SERV : service sched1 j (time_after_last_execution job_arrival sched2 j t) =
      service sched2 j (time_after_last_execution job_arrival sched2 j t) :=
    service_congr sched1 sched2 j _ (fun i hi => SCH j i (by omega'))
  simp only [pending, COMP, suspended_at, suspension_duration, TALE, SERV]
  rfl

theorem scheduler_uses_construction_function {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time) (arr_seq : arrival_sequence Job)
    (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq)
    (next_suspension : job_suspension Job) (higher_eq_priority : JLDP_policy Job) :
    ∀ t, (scheduler job_arrival job_cost arr_seq next_suspension higher_eq_priority) t = highest_priority_job job_arrival job_cost arr_seq next_suspension higher_eq_priority (scheduler job_arrival job_cost arr_seq next_suspension higher_eq_priority) t := by
  intro t
  exact prefix_dependent_schedule_construction _ _ (scheduler_depends_only_on_prefix job_arrival job_cost arr_seq H_arrival_times_are_consistent next_suspension higher_eq_priority) t

/-- LEAN_HELPER: a scheduled job is one of the pending, non-suspended jobs. -/
private theorem scheduled_in_pending_jobs {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time) (arr_seq : arrival_sequence Job)
    (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq)
    (next_suspension : job_suspension Job) (higher_eq_priority : JLDP_policy Job) (j : Job) (t : time)
    (SCHED : scheduled_at (scheduler job_arrival job_cost arr_seq next_suspension higher_eq_priority) j t = true) :
    j ∈ jobs_arrived_up_to arr_seq t ∧ pending job_arrival job_cost (scheduler job_arrival job_cost arr_seq next_suspension higher_eq_priority) j t = true ∧
      (!suspended_at job_arrival job_cost next_suspension (scheduler job_arrival job_cost arr_seq next_suspension higher_eq_priority) j t) = true := by
  simp only [scheduled_at, decide_eq_true_eq] at SCHED
  rw [scheduler_uses_construction_function job_arrival job_cost arr_seq H_arrival_times_are_consistent next_suspension higher_eq_priority] at SCHED
  have IN := seq_min_in_seq _ _ _ SCHED
  unfold pending_jobs at IN
  rw [List.mem_filter, Bool.and_eq_true] at IN
  exact ⟨IN.1, IN.2.1, IN.2.2⟩

/-! ### Properties of the scheduler -/

theorem scheduler_jobs_come_from_arrival_sequence {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time) (arr_seq : arrival_sequence Job)
    (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq)
    (next_suspension : job_suspension Job) (higher_eq_priority : JLDP_policy Job) :
    jobs_come_from_arrival_sequence (scheduler job_arrival job_cost arr_seq next_suspension higher_eq_priority) arr_seq := by
  intro j t SCHED
  exact in_arrivals_implies_arrived arr_seq j 0 (t + 1) (scheduled_in_pending_jobs job_arrival job_cost arr_seq H_arrival_times_are_consistent next_suspension higher_eq_priority j t SCHED).1

theorem scheduler_jobs_must_arrive_to_execute {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time) (arr_seq : arrival_sequence Job)
    (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq)
    (next_suspension : job_suspension Job) (higher_eq_priority : JLDP_policy Job) :
    jobs_must_arrive_to_execute job_arrival (scheduler job_arrival job_cost arr_seq next_suspension higher_eq_priority) := by
  intro j t SCHED
  have PEND := (scheduled_in_pending_jobs job_arrival job_cost arr_seq H_arrival_times_are_consistent next_suspension higher_eq_priority j t SCHED).2.1
  simp only [pending, Bool.and_eq_true] at PEND
  exact PEND.1

theorem scheduler_completed_jobs_dont_execute {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time) (arr_seq : arrival_sequence Job)
    (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq)
    (next_suspension : job_suspension Job) (higher_eq_priority : JLDP_policy Job) :
    completed_jobs_dont_execute job_cost (scheduler job_arrival job_cost arr_seq next_suspension higher_eq_priority) := by
  intro j t
  induction t with
  | zero => simp [service, service_during]
  | succ t IHt =>
    have STEP : service (scheduler job_arrival job_cost arr_seq next_suspension higher_eq_priority) j (t + 1) = service (scheduler job_arrival job_cost arr_seq next_suspension higher_eq_priority) j t + service_at (scheduler job_arrival job_cost arr_seq next_suspension higher_eq_priority) j t := by
      unfold service service_during
      rw [Finset.sum_Ico_succ_top (Nat.zero_le _)]
    rw [STEP]
    rcases Nat.lt_or_ge (service (scheduler job_arrival job_cost arr_seq next_suspension higher_eq_priority) j t) (job_cost j) with LT | GE
    · have : service_at (scheduler job_arrival job_cost arr_seq next_suspension higher_eq_priority) j t ≤ 1 := by
        unfold service_at; cases scheduled_at _ j t <;> simp
      omega'
    · have NS : scheduled_at (scheduler job_arrival job_cost arr_seq next_suspension higher_eq_priority) j t = false := by
        cases hs : scheduled_at (scheduler job_arrival job_cost arr_seq next_suspension higher_eq_priority) j t
        · rfl
        · have PEND := (scheduled_in_pending_jobs job_arrival job_cost arr_seq H_arrival_times_are_consistent next_suspension higher_eq_priority j t hs).2.1
          simp only [pending, completed_by, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at PEND
          exact absurd GE PEND.2
      simp only [service_at, NS, Bool.toNat_false, Nat.add_zero]
      exact IHt

/-- LEAN_HELPER: a backlogged job of the arrival sequence is one of the pending, non-suspended jobs. -/
private theorem backlogged_in_pending_jobs {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time) (arr_seq : arrival_sequence Job)
    (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq)
    (next_suspension : job_suspension Job) (higher_eq_priority : JLDP_policy Job) (j : Job) (t : time) (IN : arrives_in arr_seq j)
    (BACK : Prosa.Classic.Model.Schedule.Uni.Susp.Schedule.ScheduleWithSuspensions.backlogged job_arrival job_cost
      next_suspension (scheduler job_arrival job_cost arr_seq next_suspension higher_eq_priority) j t = true) :
    j ∈ pending_jobs job_arrival job_cost arr_seq next_suspension (scheduler job_arrival job_cost arr_seq next_suspension higher_eq_priority) t := by
  simp only [Prosa.Classic.Model.Schedule.Uni.Susp.Schedule.ScheduleWithSuspensions.backlogged,
    Bool.and_eq_true] at BACK
  unfold pending_jobs
  rw [List.mem_filter]
  refine ⟨?_, by simp only [BACK.1.1, BACK.2, Bool.and_self]⟩
  have ARR := BACK.1.1
  simp only [pending, has_arrived, Bool.and_eq_true, decide_eq_true_eq] at ARR
  exact arrived_between_implies_in_arrivals job_arrival arr_seq H_arrival_times_are_consistent j 0 (t + 1) IN
    (by simp only [arrived_between, Bool.and_eq_true, decide_eq_true_eq]; omega')

theorem scheduler_work_conserving {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time) (arr_seq : arrival_sequence Job)
    (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq)
    (next_suspension : job_suspension Job) (higher_eq_priority : JLDP_policy Job) :
    work_conserving job_arrival job_cost next_suspension arr_seq (scheduler job_arrival job_cost arr_seq next_suspension higher_eq_priority) := by
  intro j t IN BACK
  have PEND := backlogged_in_pending_jobs job_arrival job_cost arr_seq H_arrival_times_are_consistent next_suspension higher_eq_priority j t IN BACK
  have EX := seq_min_exists (higher_eq_priority t) _ j PEND
  cases HP : highest_priority_job job_arrival job_cost arr_seq next_suspension higher_eq_priority (scheduler job_arrival job_cost arr_seq next_suspension higher_eq_priority) t with
  | none =>
    unfold highest_priority_job at HP
    rw [HP] at EX; simp at EX
  | some j_hp =>
    refine ⟨j_hp, ?_⟩
    simp only [scheduled_at, decide_eq_true_eq]
    rw [scheduler_uses_construction_function job_arrival job_cost arr_seq H_arrival_times_are_consistent next_suspension higher_eq_priority, HP]

theorem scheduler_respects_policy {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time) (arr_seq : arrival_sequence Job)
    (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq)
    (next_suspension : job_suspension Job) (higher_eq_priority : JLDP_policy Job)
    (H_priority_is_transitive : JLDP_is_transitive higher_eq_priority)
    (H_priority_is_total : JLDP_is_total arr_seq higher_eq_priority) :
    respects_JLDP_policy job_arrival job_cost next_suspension arr_seq (scheduler job_arrival job_cost arr_seq next_suspension higher_eq_priority) higher_eq_priority := by
  intro j1 j2 t ARR1 BACK SCHED
  have IN := backlogged_in_pending_jobs job_arrival job_cost arr_seq H_arrival_times_are_consistent next_suspension higher_eq_priority j1 t ARR1 BACK
  simp only [scheduled_at, decide_eq_true_eq] at SCHED
  rw [scheduler_uses_construction_function job_arrival job_cost arr_seq H_arrival_times_are_consistent next_suspension higher_eq_priority] at SCHED
  apply seq_min_computes_min (higher_eq_priority t) (H_priority_is_transitive t) _ _ j2 j1 SCHED IN
  intro x y INx INy
  unfold pending_jobs at INx INy
  exact H_priority_is_total x y t (in_arrivals_implies_arrived arr_seq x 0 (t + 1) (List.mem_filter.mp INx).1)
    (in_arrivals_implies_arrived arr_seq y 0 (t + 1) (List.mem_filter.mp INy).1)

theorem scheduler_respects_self_suspensions {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time) (arr_seq : arrival_sequence Job)
    (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq)
    (next_suspension : job_suspension Job) (higher_eq_priority : JLDP_policy Job) :
    respects_self_suspensions job_arrival job_cost next_suspension (scheduler job_arrival job_cost arr_seq next_suspension higher_eq_priority) := by
  intro j t SCHED SUSP
  have NS := (scheduled_in_pending_jobs job_arrival job_cost arr_seq H_arrival_times_are_consistent next_suspension higher_eq_priority j t SCHED).2.2
  rw [SUSP] at NS; exact absurd NS (by simp)

end Prosa.Classic.Implementation.Uni.Susp.Schedule.ConcreteScheduler
