-- Authoritative source:
-- ProsaBuddy classic Prosa (prosabuddy commit f692cb7479780cf6009493f373a309e13165201c)
-- source: classic/implementation/uni/jitter/schedule.v
-- sha256: see Prosa-Shunqi/classic-prosa/comprehensive-classic/file_order.csv (rank 96)

import Prosa.Classic.Util.All
import Prosa.Classic.Model.Arrival.Basic.Job
import Prosa.Classic.Model.Arrival.Basic.ArrivalSequence
import Prosa.Classic.Model.Priority
import Prosa.Classic.Model.Schedule.Uni.Jitter.Schedule
import Prosa.Classic.Model.Schedule.Uni.Jitter.Platform
import Prosa.Classic.Model.Schedule.Uni.Transformation.Construction

/-!
A concrete jitter-aware priority-based uniprocessor scheduler (Rocq module `ConcreteScheduler` of
`implementation/uni/jitter/schedule.v`).

Representation notes (as in `classic/implementation/uni/basic/schedule.v`):
* `[seq j <- s | P j]` is `s.filter P`; `seq_min` is the classic `Prosa.Classic.Util.Minmax.seq_min`;
  `pending`/`backlogged` are the jitter-aware `UniprocessorScheduleWithJitter` definitions and
  `work_conserving`/`respects_JLDP_policy` the jitter-aware `Platform` ones.
* The section-local `Let`s (`is_pending`, `empty_schedule`, `sched`) are unfolded.
* Binder lists follow the Rocq contract (the `Implementation` section has no consistency hypothesis; in the
  `Proofs` section only `scheduler_work_conserving` and `scheduler_respects_policy` take
  `H_arrival_times_are_consistent`, and only the latter takes `H_priority_is_transitive`/`H_priority_is_total`).
-/

set_option linter.unusedVariables false

namespace Prosa.Classic.Implementation.Uni.Jitter.Schedule.ConcreteScheduler

open Prosa.Classic.Model.Time.Time
open Prosa.Classic.Model.Arrival.Basic.ArrivalSequence.ArrivalSequence
open Prosa.Classic.Model.Arrival.Jitter.ArrivalSequence.ArrivalSequenceWithJitter
open Prosa.Classic.Model.Priority.Priority
open Prosa.Classic.Model.Schedule.Uni.Schedule.UniprocessorSchedule hiding pending backlogged scheduled_implies_pending
open Prosa.Classic.Model.Schedule.Uni.Jitter.Schedule.UniprocessorScheduleWithJitter
open Prosa.Classic.Model.Schedule.Uni.Jitter.Platform.Platform
open Prosa.Classic.Model.Schedule.Uni.Transformation.Construction.ScheduleConstruction
open Prosa.Classic.Util.Minmax (seq_min seq_min_in_seq seq_min_exists seq_min_computes_min)

universe u

local macro "omega'" : tactic =>
  `(tactic| ((try dsimp only [Prosa.Classic.Model.Time.Time.time,
    Prosa.Classic.Model.Time.Time.instant, Prosa.Classic.Model.Time.Time.duration] at *) <;>
    omega))

def pending_jobs {Job : Type u} [DecidableEq Job] (job_arrival job_cost job_jitter : Job → time)
    (arr_seq : arrival_sequence Job) (sched_prefix : schedule Job) (t : time) : List Job :=
  (actual_arrivals_up_to job_arrival job_jitter arr_seq t).filter
    (fun j => pending job_arrival job_cost job_jitter sched_prefix j t)

def highest_priority_job {Job : Type u} [DecidableEq Job] (job_arrival job_cost job_jitter : Job → time)
    (arr_seq : arrival_sequence Job) (higher_eq_priority : JLDP_policy Job) (sched_prefix : schedule Job)
    (t : time) : Option Job :=
  seq_min (higher_eq_priority t) (pending_jobs job_arrival job_cost job_jitter arr_seq sched_prefix t)

def scheduler {Job : Type u} [DecidableEq Job] (job_arrival job_cost job_jitter : Job → time)
    (arr_seq : arrival_sequence Job) (higher_eq_priority : JLDP_policy Job) : schedule Job :=
  build_schedule_from_prefixes (highest_priority_job job_arrival job_cost job_jitter arr_seq higher_eq_priority)
    (fun _ => none)

theorem scheduler_depends_only_on_prefix {Job : Type u} [DecidableEq Job]
    (job_arrival job_cost job_jitter : Job → time) (arr_seq : arrival_sequence Job)
    (higher_eq_priority : JLDP_policy Job) :
    ∀ (sched1 sched2 : schedule Job) (t : Nat), (∀ t0, t0 < t → sched1 t0 = sched2 t0) →
      highest_priority_job job_arrival job_cost job_jitter arr_seq higher_eq_priority sched1 t =
        highest_priority_job job_arrival job_cost job_jitter arr_seq higher_eq_priority sched2 t := by
  intro sched1 sched2 t ALL
  unfold highest_priority_job pending_jobs
  congr 2
  funext j
  have SERV : service sched1 j t = service sched2 j t := by
    unfold service service_during
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_Ico] at hi
    simp only [service_at, scheduled_at, ALL i hi.2]
  simp only [pending, completed_by, SERV]

theorem scheduler_uses_construction_function {Job : Type u} [DecidableEq Job]
    (job_arrival job_cost job_jitter : Job → time) (arr_seq : arrival_sequence Job)
    (higher_eq_priority : JLDP_policy Job) :
    ∀ t, scheduler job_arrival job_cost job_jitter arr_seq higher_eq_priority t =
      highest_priority_job job_arrival job_cost job_jitter arr_seq higher_eq_priority
        (scheduler job_arrival job_cost job_jitter arr_seq higher_eq_priority) t := by
  intro t
  exact prefix_dependent_schedule_construction _ _
    (scheduler_depends_only_on_prefix job_arrival job_cost job_jitter arr_seq higher_eq_priority) t

/-- LEAN_HELPER: a scheduled job is one of the pending jobs. -/
private theorem scheduled_in_pending_jobs {Job : Type u} [DecidableEq Job]
    (job_arrival job_cost job_jitter : Job → time) (arr_seq : arrival_sequence Job)
    (higher_eq_priority : JLDP_policy Job) (j : Job) (t : time)
    (SCHED : scheduled_at (scheduler job_arrival job_cost job_jitter arr_seq higher_eq_priority) j t = true) :
    j ∈ pending_jobs job_arrival job_cost job_jitter arr_seq
      (scheduler job_arrival job_cost job_jitter arr_seq higher_eq_priority) t := by
  simp only [scheduled_at, decide_eq_true_eq] at SCHED
  rw [scheduler_uses_construction_function job_arrival job_cost job_jitter arr_seq] at SCHED
  exact seq_min_in_seq _ _ _ SCHED

theorem scheduler_jobs_come_from_arrival_sequence {Job : Type u} [DecidableEq Job]
    (job_arrival job_cost job_jitter : Job → time) (arr_seq : arrival_sequence Job)
    (higher_eq_priority : JLDP_policy Job) :
    jobs_come_from_arrival_sequence (scheduler job_arrival job_cost job_jitter arr_seq higher_eq_priority) arr_seq := by
  intro j t SCHED
  have IN := scheduled_in_pending_jobs job_arrival job_cost job_jitter arr_seq higher_eq_priority j t SCHED
  unfold pending_jobs at IN
  rw [List.mem_filter] at IN
  exact in_actual_arrivals_between_implies_arrived job_arrival job_jitter arr_seq j 0 (t + 1) IN.1

theorem scheduler_jobs_execute_after_jitter {Job : Type u} [DecidableEq Job]
    (job_arrival job_cost job_jitter : Job → time) (arr_seq : arrival_sequence Job)
    (higher_eq_priority : JLDP_policy Job) :
    jobs_execute_after_jitter job_arrival job_jitter
      (scheduler job_arrival job_cost job_jitter arr_seq higher_eq_priority) := by
  intro j t SCHED
  have IN := scheduled_in_pending_jobs job_arrival job_cost job_jitter arr_seq higher_eq_priority j t SCHED
  unfold pending_jobs at IN
  rw [List.mem_filter] at IN
  simp only [pending, Bool.and_eq_true] at IN
  exact IN.2.1

theorem scheduler_completed_jobs_dont_execute {Job : Type u} [DecidableEq Job]
    (job_arrival job_cost job_jitter : Job → time) (arr_seq : arrival_sequence Job)
    (higher_eq_priority : JLDP_policy Job) :
    completed_jobs_dont_execute job_cost (scheduler job_arrival job_cost job_jitter arr_seq higher_eq_priority) := by
  intro j t
  induction t with
  | zero => simp [service, service_during]
  | succ t IHt =>
    have STEP : service (scheduler job_arrival job_cost job_jitter arr_seq higher_eq_priority) j (t + 1) =
        service (scheduler job_arrival job_cost job_jitter arr_seq higher_eq_priority) j t +
          service_at (scheduler job_arrival job_cost job_jitter arr_seq higher_eq_priority) j t := by
      unfold service service_during
      rw [Finset.sum_Ico_succ_top (Nat.zero_le _)]
    rw [STEP]
    rcases Nat.lt_or_ge (service (scheduler job_arrival job_cost job_jitter arr_seq higher_eq_priority) j t)
      (job_cost j) with LT | GE
    · have : service_at (scheduler job_arrival job_cost job_jitter arr_seq higher_eq_priority) j t ≤ 1 := by
        unfold service_at; cases scheduled_at _ j t <;> simp
      omega'
    · have NS : scheduled_at (scheduler job_arrival job_cost job_jitter arr_seq higher_eq_priority) j t = false := by
        cases hs : scheduled_at (scheduler job_arrival job_cost job_jitter arr_seq higher_eq_priority) j t
        · rfl
        · have IN := scheduled_in_pending_jobs job_arrival job_cost job_jitter arr_seq higher_eq_priority j t hs
          unfold pending_jobs at IN
          rw [List.mem_filter] at IN
          simp only [pending, completed_by, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at IN
          exact absurd GE IN.2.2
      simp only [service_at, NS, Bool.toNat_false, Nat.add_zero]
      exact IHt

/-- LEAN_HELPER: a backlogged job that arrives in the sequence is one of the pending jobs. -/
private theorem backlogged_in_pending_jobs {Job : Type u} [DecidableEq Job]
    (job_arrival job_cost job_jitter : Job → time) (arr_seq : arrival_sequence Job)
    (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq)
    (sched : schedule Job) (j : Job) (t : time) (IN : arrives_in arr_seq j)
    (BACK : backlogged job_arrival job_cost job_jitter sched j t = true) :
    j ∈ pending_jobs job_arrival job_cost job_jitter arr_seq sched t := by
  simp only [backlogged, Bool.and_eq_true] at BACK
  unfold pending_jobs
  rw [List.mem_filter]
  refine ⟨?_, BACK.1⟩
  have ARR := BACK.1
  simp only [pending, Bool.and_eq_true] at ARR
  have PASS := of_decide_eq_true ARR.1
  exact arrived_between_implies_in_actual_arrivals job_arrival job_jitter arr_seq H_arrival_times_are_consistent j 0
    (t + 1) IN (by simp only [actual_arrival_between, Bool.and_eq_true, decide_eq_true_eq]; omega')

theorem scheduler_work_conserving {Job : Type u} [DecidableEq Job]
    (job_arrival job_cost job_jitter : Job → time) (arr_seq : arrival_sequence Job)
    (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq)
    (higher_eq_priority : JLDP_policy Job) :
    work_conserving job_arrival job_cost job_jitter arr_seq
      (scheduler job_arrival job_cost job_jitter arr_seq higher_eq_priority) := by
  intro j t IN BACK
  have PEND := backlogged_in_pending_jobs job_arrival job_cost job_jitter arr_seq H_arrival_times_are_consistent _
    j t IN BACK
  have EX := seq_min_exists (higher_eq_priority t) _ j PEND
  cases HP : highest_priority_job job_arrival job_cost job_jitter arr_seq higher_eq_priority
      (scheduler job_arrival job_cost job_jitter arr_seq higher_eq_priority) t with
  | none =>
    unfold highest_priority_job at HP
    rw [HP] at EX; simp at EX
  | some j_hp =>
    refine ⟨j_hp, ?_⟩
    simp only [scheduled_at, decide_eq_true_eq]
    rw [scheduler_uses_construction_function job_arrival job_cost job_jitter arr_seq, HP]

theorem scheduler_respects_policy {Job : Type u} [DecidableEq Job]
    (job_arrival job_cost job_jitter : Job → time) (arr_seq : arrival_sequence Job)
    (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq)
    (higher_eq_priority : JLDP_policy Job) (H_priority_is_transitive : JLDP_is_transitive higher_eq_priority)
    (H_priority_is_total : JLDP_is_total arr_seq higher_eq_priority) :
    respects_JLDP_policy job_arrival job_cost job_jitter arr_seq
      (scheduler job_arrival job_cost job_jitter arr_seq higher_eq_priority) higher_eq_priority := by
  intro j1 j2 t ARR1 BACK SCHED
  have IN := backlogged_in_pending_jobs job_arrival job_cost job_jitter arr_seq H_arrival_times_are_consistent _
    j1 t ARR1 BACK
  simp only [scheduled_at, decide_eq_true_eq] at SCHED
  rw [scheduler_uses_construction_function job_arrival job_cost job_jitter arr_seq] at SCHED
  refine seq_min_computes_min (higher_eq_priority t) (H_priority_is_transitive t) _ ?_ j2 j1 SCHED IN
  intro x y INx INy
  unfold pending_jobs at INx INy
  rw [List.mem_filter] at INx INy
  exact H_priority_is_total x y t
    (in_actual_arrivals_between_implies_arrived job_arrival job_jitter arr_seq x 0 (t + 1) INx.1)
    (in_actual_arrivals_between_implies_arrived job_arrival job_jitter arr_seq y 0 (t + 1) INy.1)

end Prosa.Classic.Implementation.Uni.Jitter.Schedule.ConcreteScheduler
