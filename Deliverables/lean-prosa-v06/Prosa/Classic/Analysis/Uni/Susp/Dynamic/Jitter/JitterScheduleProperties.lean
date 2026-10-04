-- Authoritative source:
-- ProsaBuddy classic Prosa (prosabuddy commit f692cb7479780cf6009493f373a309e13165201c)
-- source: classic/analysis/uni/susp/dynamic/jitter/jitter_schedule_properties.v
-- sha256: see Prosa-Shunqi/classic-prosa/comprehensive-classic/file_order.csv (rank 149)

import Prosa.Classic.Util.All
import Prosa.Classic.Model.Priority
import Prosa.Classic.Model.Suspension
import Prosa.Classic.Model.Arrival.Basic.Job
import Prosa.Classic.Model.Arrival.Basic.Task
import Prosa.Classic.Model.Arrival.Basic.ArrivalSequence
import Prosa.Classic.Model.Arrival.Jitter.Job
import Prosa.Classic.Model.Schedule.Uni.Schedulability
import Prosa.Classic.Model.Schedule.Uni.Service
import Prosa.Classic.Model.Schedule.Uni.Workload
import Prosa.Classic.Model.Schedule.Uni.ResponseTime
import Prosa.Classic.Model.Schedule.Uni.Jitter.Schedule
import Prosa.Classic.Model.Schedule.Uni.Jitter.ValidSchedule
import Prosa.Classic.Model.Schedule.Uni.Jitter.Platform
import Prosa.Classic.Model.Schedule.Uni.Susp.SuspensionIntervals
import Prosa.Classic.Model.Schedule.Uni.Susp.Schedule
import Prosa.Classic.Model.Schedule.Uni.Susp.ValidSchedule
import Prosa.Classic.Model.Schedule.Uni.Susp.Platform
import Prosa.Classic.Analysis.Uni.Susp.Dynamic.Jitter.JitterSchedule
import Prosa.Classic.Model.Schedule.Uni.Transformation.Construction

/-!
Properties of the jitter-aware schedule constructed from a suspension-aware schedule (Rocq module
`JitterScheduleProperties` of `classic/analysis/uni/susp/dynamic/jitter/jitter_schedule_properties.v`).

Representation notes:
* The Rocq module aliases (`basic`, `susp`, `jitter_aware`, `susp_aware`, `job_jitter`, `reduction`) are Lean
  namespace abbreviations of the accepted modules (`reduction` is `JitterScheduleConstruction`).
* `x != y` in proposition position is `(!decide (x = y)) = true`; `~~ b` is `(!b) = true`.
* The section-local `Let`s (`job_higher_eq_priority`, `job_response_time_in_sched_susp_bounded_by`, `arr_j`,
  `task_of_j`, `other_hep_task`, `sched_jitter`, `inflated_job_cost`, `job_jitter`, `build_schedule`,
  `pending_jobs_other_than_j`, `hp_job_other_than_j`, `is_valid_jitter_aware_schedule`) are unfolded.
* Binder lists follow the Rocq contract (the statement-level job of the `jobs_come_from_arrival_sequence`-style
  properties is bound by those definitions; the section job is `j`).
-/

set_option linter.dupNamespace false
set_option linter.unusedVariables false

namespace Prosa.Classic.Analysis.Uni.Susp.Dynamic.Jitter.JitterScheduleProperties.JitterScheduleProperties

open Prosa.Classic.Model.Time.Time
open Prosa.Classic.Model.Arrival.Basic.ArrivalSequence.ArrivalSequence
open Prosa.Classic.Model.Arrival.Jitter.ArrivalSequence.ArrivalSequenceWithJitter
open Prosa.Classic.Model.Priority.Priority
open Prosa.Classic.Model.Suspension.Suspension
open Prosa.Classic.Model.Schedule.Uni.Schedule.UniprocessorSchedule hiding pending backlogged scheduled_implies_pending
open Prosa.Classic.Model.Schedule.Uni.Jitter.Schedule.UniprocessorScheduleWithJitter
open Prosa.Classic.Model.Schedule.Uni.Jitter.ValidSchedule.ValidJitterAwareSchedule
open Prosa.Classic.Model.Schedule.Uni.Susp.ValidSchedule.ValidSuspensionAwareSchedule
open Prosa.Classic.Model.Schedule.Uni.Transformation.Construction.ScheduleConstruction
open Prosa.Classic.Util.Minmax (seq_min seq_min_in_seq seq_min_exists seq_min_computes_min)

namespace reduction
export Prosa.Classic.Analysis.Uni.Susp.Dynamic.Jitter.JitterSchedule.JitterScheduleConstruction
  (inflated_job_cost job_jitter pending_jobs_other_than_j highest_priority_job_other_than_j build_schedule sched_jitter)
end reduction
namespace jitter_aware
export Prosa.Classic.Model.Schedule.Uni.Jitter.Platform.Platform (work_conserving respects_FP_policy)
end jitter_aware

universe u v

local macro "omega'" : tactic =>
  `(tactic| ((try dsimp only [Prosa.Classic.Model.Time.Time.time,
    Prosa.Classic.Model.Time.Time.instant, Prosa.Classic.Model.Time.Time.duration] at *) <;>
    omega))

/-! ### Schedule construction -/

theorem sched_jitter_depends_only_on_service {Task : Type u} [DecidableEq Task] {Job : Type v} [DecidableEq Job] (job_arrival : Job → time) (job_task : Job → Task) (arr_seq : arrival_sequence Job) (higher_eq_priority : FP_policy Task) (job_cost : Job → time) (job_suspension_duration : job_suspension Job) (j : Job)
    (R : Job → time) :
    ∀ (sched1 sched2 : schedule Job) (t : time), (∀ j, service sched1 j t = service sched2 j t) →
      reduction.build_schedule job_arrival job_task arr_seq higher_eq_priority job_cost job_suspension_duration j R sched1 t = reduction.build_schedule job_arrival job_task arr_seq higher_eq_priority job_cost job_suspension_duration j R sched2 t := by
  intro sched1 sched2 t ALL
  have SAME : ∀ x, pending job_arrival (reduction.inflated_job_cost job_cost job_suspension_duration j) (reduction.job_jitter job_arrival job_task higher_eq_priority job_cost j R) sched1 x t = pending job_arrival (reduction.inflated_job_cost job_cost job_suspension_duration j) (reduction.job_jitter job_arrival job_task higher_eq_priority job_cost j R) sched2 x t := by
    intro x; simp only [pending, completed_by, ALL]
  unfold reduction.build_schedule reduction.highest_priority_job_other_than_j reduction.pending_jobs_other_than_j
  simp only [SAME]

theorem sched_jitter_uses_construction_function {Task : Type u} [DecidableEq Task] {Job : Type v} [DecidableEq Job] (job_arrival : Job → time) (job_task : Job → Task) (arr_seq : arrival_sequence Job) (higher_eq_priority : FP_policy Task) (job_cost : Job → time) (job_suspension_duration : job_suspension Job) (j : Job)
    (R : Job → time) :
    ∀ t, (reduction.sched_jitter job_arrival job_task arr_seq higher_eq_priority job_cost job_suspension_duration j R) t = reduction.build_schedule job_arrival job_task arr_seq higher_eq_priority job_cost job_suspension_duration j R (reduction.sched_jitter job_arrival job_task arr_seq higher_eq_priority job_cost job_suspension_duration j R) t := by
  intro t
  exact service_dependent_schedule_construction _ _
    (sched_jitter_depends_only_on_service job_arrival job_task arr_seq higher_eq_priority job_cost job_suspension_duration j R) t

/-! ### Proof-local facts -/

/-- LEAN_HELPER: membership in the list of pending jobs other than `j`. -/
private theorem mem_pjo {Task : Type u} [DecidableEq Task] {Job : Type v} [DecidableEq Job] (job_arrival : Job → time) (job_task : Job → Task) (arr_seq : arrival_sequence Job) (higher_eq_priority : FP_policy Task) (job_cost : Job → time) (job_suspension_duration : job_suspension Job) (j : Job) (R : Job → time)
    (sched : schedule Job) (t : time) (x : Job) :
    x ∈ reduction.pending_jobs_other_than_j job_arrival job_task arr_seq higher_eq_priority job_cost job_suspension_duration j R sched t ↔
      x ∈ actual_arrivals_up_to job_arrival (reduction.job_jitter job_arrival job_task higher_eq_priority job_cost j R) arr_seq t ∧ pending job_arrival (reduction.inflated_job_cost job_cost job_suspension_duration j) (reduction.job_jitter job_arrival job_task higher_eq_priority job_cost j R) sched x t = true ∧ x ≠ j := by
  unfold reduction.pending_jobs_other_than_j
  rw [List.mem_filter]
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not]

/-- LEAN_HELPER: a pending job other than `j` of the arrival sequence is in the list. -/
private theorem pending_in_pjo {Task : Type u} [DecidableEq Task] {Job : Type v} [DecidableEq Job] (job_arrival : Job → time) (job_task : Job → Task) (arr_seq : arrival_sequence Job) (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq) (higher_eq_priority : FP_policy Task) (job_cost : Job → time) (job_suspension_duration : job_suspension Job) (j : Job)
    (R : Job → time) (sched : schedule Job) (t : time) (x : Job) (ARR : arrives_in arr_seq x)
    (PEND : pending job_arrival (reduction.inflated_job_cost job_cost job_suspension_duration j) (reduction.job_jitter job_arrival job_task higher_eq_priority job_cost j R) sched x t = true) (NEQ : x ≠ j) : x ∈ reduction.pending_jobs_other_than_j job_arrival job_task arr_seq higher_eq_priority job_cost job_suspension_duration j R sched t := by
  rw [mem_pjo]
  refine ⟨?_, PEND, NEQ⟩
  have JP := PEND
  simp only [pending, Bool.and_eq_true] at JP
  have JP1 := of_decide_eq_true JP.1
  exact arrived_between_implies_in_actual_arrivals job_arrival _ arr_seq H_arrival_times_are_consistent x 0 (t + 1)
    ARR (by simp only [actual_arrival_between, Bool.and_eq_true, decide_eq_true_eq]; omega')

/-- LEAN_HELPER: the job scheduled by the construction is pending and is either `j` or a pending job other
than `j`. -/
private theorem scheduled_facts {Task : Type u} [DecidableEq Task] {Job : Type v} [DecidableEq Job] (job_arrival : Job → time) (job_task : Job → Task) (arr_seq : arrival_sequence Job) (higher_eq_priority : FP_policy Task) (job_cost : Job → time) (job_suspension_duration : job_suspension Job) (j : Job) (R : Job → time)
    (t : time) (x : Job) (SCHED : (reduction.sched_jitter job_arrival job_task arr_seq higher_eq_priority job_cost job_suspension_duration j R) t = some x) :
    pending job_arrival (reduction.inflated_job_cost job_cost job_suspension_duration j) (reduction.job_jitter job_arrival job_task higher_eq_priority job_cost j R) (reduction.sched_jitter job_arrival job_task arr_seq higher_eq_priority job_cost job_suspension_duration j R) x t = true ∧ (x = j ∨ x ∈ reduction.pending_jobs_other_than_j job_arrival job_task arr_seq higher_eq_priority job_cost job_suspension_duration j R (reduction.sched_jitter job_arrival job_task arr_seq higher_eq_priority job_cost job_suspension_duration j R) t) := by
  rw [sched_jitter_uses_construction_function job_arrival job_task arr_seq higher_eq_priority job_cost job_suspension_duration j R] at SCHED
  unfold reduction.build_schedule at SCHED
  have INL : ∀ y, reduction.highest_priority_job_other_than_j job_arrival job_task arr_seq higher_eq_priority job_cost job_suspension_duration j R (reduction.sched_jitter job_arrival job_task arr_seq higher_eq_priority job_cost job_suspension_duration j R) t = some y → y ∈ reduction.pending_jobs_other_than_j job_arrival job_task arr_seq higher_eq_priority job_cost job_suspension_duration j R (reduction.sched_jitter job_arrival job_task arr_seq higher_eq_priority job_cost job_suspension_duration j R) t := fun y h => seq_min_in_seq _ _ _ h
  have PL : ∀ y, y ∈ reduction.pending_jobs_other_than_j job_arrival job_task arr_seq higher_eq_priority job_cost job_suspension_duration j R (reduction.sched_jitter job_arrival job_task arr_seq higher_eq_priority job_cost job_suspension_duration j R) t → pending job_arrival (reduction.inflated_job_cost job_cost job_suspension_duration j) (reduction.job_jitter job_arrival job_task higher_eq_priority job_cost j R) (reduction.sched_jitter job_arrival job_task arr_seq higher_eq_priority job_cost job_suspension_duration j R) y t = true := fun y h => ((mem_pjo job_arrival job_task arr_seq higher_eq_priority job_cost job_suspension_duration j R _ t y).mp h).2.1
  split at SCHED
  · next PJ =>
    cases HP : reduction.highest_priority_job_other_than_j job_arrival job_task arr_seq higher_eq_priority job_cost job_suspension_duration j R (reduction.sched_jitter job_arrival job_task arr_seq higher_eq_priority job_cost job_suspension_duration j R) t with
    | none =>
      rw [HP] at SCHED; simp only [Option.some.injEq] at SCHED; subst SCHED
      exact ⟨PJ, Or.inl rfl⟩
    | some j_hp =>
      rw [HP] at SCHED; simp only at SCHED
      split at SCHED
      · simp only [Option.some.injEq] at SCHED; subst SCHED; exact ⟨PJ, Or.inl rfl⟩
      · simp only [Option.some.injEq] at SCHED; subst SCHED
        exact ⟨PL _ (INL _ HP), Or.inr (INL _ HP)⟩
  · exact ⟨PL _ (INL _ SCHED), Or.inr (INL _ SCHED)⟩

/-! ### Valid schedule properties -/

theorem sched_jitter_jobs_come_from_arrival_sequence {Task : Type u} [DecidableEq Task] {Job : Type v} [DecidableEq Job] (job_arrival : Job → time) (job_task : Job → Task) (arr_seq : arrival_sequence Job) (higher_eq_priority : FP_policy Task) (job_cost : Job → time) (job_suspension_duration : job_suspension Job)
    (sched_susp : schedule Job)
    (H_valid_schedule : valid_suspension_aware_schedule job_arrival arr_seq (FP_to_JLDP job_task higher_eq_priority)
      job_suspension_duration job_cost sched_susp)
    (j : Job) (H_from_arrival_sequence : arrives_in arr_seq j) (R : Job → time) :
    jobs_come_from_arrival_sequence (reduction.sched_jitter job_arrival job_task arr_seq higher_eq_priority job_cost job_suspension_duration j R) arr_seq := by
  intro x t SCHED
  simp only [scheduled_at, decide_eq_true_eq] at SCHED
  rcases (scheduled_facts job_arrival job_task arr_seq higher_eq_priority job_cost job_suspension_duration j R t x SCHED).2 with EQ | IN
  · subst EQ; exact H_from_arrival_sequence
  · exact in_actual_arrivals_between_implies_arrived job_arrival _ arr_seq x 0 (t + 1)
      ((mem_pjo job_arrival job_task arr_seq higher_eq_priority job_cost job_suspension_duration j R _ t x).mp IN).1

theorem sched_jitter_jobs_execute_after_jitter {Task : Type u} [DecidableEq Task] {Job : Type v} [DecidableEq Job] (job_arrival : Job → time) (job_task : Job → Task) (arr_seq : arrival_sequence Job) (higher_eq_priority : FP_policy Task) (job_cost : Job → time) (job_suspension_duration : job_suspension Job) (j : Job)
    (H_from_arrival_sequence : arrives_in arr_seq j) (R : Job → time) :
    jobs_execute_after_jitter job_arrival (reduction.job_jitter job_arrival job_task higher_eq_priority job_cost j R) (reduction.sched_jitter job_arrival job_task arr_seq higher_eq_priority job_cost job_suspension_duration j R) := by
  intro x t SCHED
  simp only [scheduled_at, decide_eq_true_eq] at SCHED
  have P := (scheduled_facts job_arrival job_task arr_seq higher_eq_priority job_cost job_suspension_duration j R t x SCHED).1
  simp only [pending, Bool.and_eq_true] at P
  exact P.1

theorem sched_jitter_completed_jobs_dont_execute {Task : Type u} [DecidableEq Task] {Job : Type v} [DecidableEq Job] (job_arrival : Job → time) (job_task : Job → Task) (arr_seq : arrival_sequence Job) (higher_eq_priority : FP_policy Task) (job_cost : Job → time) (job_suspension_duration : job_suspension Job) (j : Job)
    (R : Job → time) :
    completed_jobs_dont_execute (reduction.inflated_job_cost job_cost job_suspension_duration j) (reduction.sched_jitter job_arrival job_task arr_seq higher_eq_priority job_cost job_suspension_duration j R) := by
  intro x t
  induction t with
  | zero => simp [service, service_during]
  | succ t IHt =>
    have STEP : service (reduction.sched_jitter job_arrival job_task arr_seq higher_eq_priority job_cost job_suspension_duration j R) x (t + 1) = service (reduction.sched_jitter job_arrival job_task arr_seq higher_eq_priority job_cost job_suspension_duration j R) x t + service_at (reduction.sched_jitter job_arrival job_task arr_seq higher_eq_priority job_cost job_suspension_duration j R) x t := by
      unfold service service_during
      rw [Finset.sum_Ico_succ_top (Nat.zero_le _)]
    rw [STEP]
    rcases Nat.lt_or_ge (service (reduction.sched_jitter job_arrival job_task arr_seq higher_eq_priority job_cost job_suspension_duration j R) x t) ((reduction.inflated_job_cost job_cost job_suspension_duration j) x) with LT | GE
    · have : service_at (reduction.sched_jitter job_arrival job_task arr_seq higher_eq_priority job_cost job_suspension_duration j R) x t ≤ 1 := by
        unfold service_at; cases scheduled_at _ x t <;> simp
      omega'
    · have NS : scheduled_at (reduction.sched_jitter job_arrival job_task arr_seq higher_eq_priority job_cost job_suspension_duration j R) x t = false := by
        cases hs : scheduled_at (reduction.sched_jitter job_arrival job_task arr_seq higher_eq_priority job_cost job_suspension_duration j R) x t
        · rfl
        · simp only [scheduled_at, decide_eq_true_eq] at hs
          have P := (scheduled_facts job_arrival job_task arr_seq higher_eq_priority job_cost job_suspension_duration j R t x hs).1
          simp only [pending, completed_by, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at P
          exact absurd GE P.2
      simp only [service_at, NS, Bool.toNat_false, Nat.add_zero]
      exact IHt

theorem sched_jitter_work_conserving {Task : Type u} [DecidableEq Task] {Job : Type v} [DecidableEq Job] (job_arrival : Job → time) (job_task : Job → Task) (arr_seq : arrival_sequence Job) (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq) (higher_eq_priority : FP_policy Task) (job_cost : Job → time) (job_suspension_duration : job_suspension Job) (j : Job)
    (R : Job → time) :
    jitter_aware.work_conserving job_arrival (reduction.inflated_job_cost job_cost job_suspension_duration j) (reduction.job_jitter job_arrival job_task higher_eq_priority job_cost j R) arr_seq (reduction.sched_jitter job_arrival job_task arr_seq higher_eq_priority job_cost job_suspension_duration j R) := by
  intro x t IN BACK
  simp only [backlogged, Bool.and_eq_true] at BACK
  simp only [scheduled_at, decide_eq_true_eq]
  rw [sched_jitter_uses_construction_function job_arrival job_task arr_seq higher_eq_priority job_cost job_suspension_duration j R]
  unfold reduction.build_schedule
  split
  · cases reduction.highest_priority_job_other_than_j job_arrival job_task arr_seq higher_eq_priority job_cost job_suspension_duration j R (reduction.sched_jitter job_arrival job_task arr_seq higher_eq_priority job_cost job_suspension_duration j R) t with
    | none => exact ⟨j, rfl⟩
    | some j_hp =>
      simp only
      split
      · exact ⟨j, rfl⟩
      · exact ⟨j_hp, rfl⟩
  · next PJ =>
    have NEQ : x ≠ j := by
      intro EQ; subst EQ; exact PJ BACK.1
    have INx := pending_in_pjo job_arrival job_task arr_seq H_arrival_times_are_consistent higher_eq_priority job_cost job_suspension_duration j R _ t x IN BACK.1 NEQ
    have EX := seq_min_exists (FP_to_JLFP job_task higher_eq_priority) _ x INx
    cases HP : reduction.highest_priority_job_other_than_j job_arrival job_task arr_seq higher_eq_priority job_cost job_suspension_duration j R (reduction.sched_jitter job_arrival job_task arr_seq higher_eq_priority job_cost job_suspension_duration j R) t with
    | none =>
      unfold reduction.highest_priority_job_other_than_j at HP
      rw [HP] at EX; simp at EX
    | some j_hp => exact ⟨j_hp, rfl⟩

/-- LEAN_HELPER: the job picked among the pending jobs other than `j` has higher-or-equal priority than all of
them. -/
private theorem hp_is_min {Task : Type u} [DecidableEq Task] {Job : Type v} [DecidableEq Job] (job_arrival : Job → time) (job_task : Job → Task) (ts : List Task) (arr_seq : arrival_sequence Job) (H_jobs_from_taskset : ∀ j, arrives_in arr_seq j → job_task j ∈ ts) (higher_eq_priority : FP_policy Task) (H_priority_is_transitive : FP_is_transitive higher_eq_priority) (H_priority_is_total : FP_is_total_over_task_set higher_eq_priority ts) (job_cost : Job → time) (job_suspension_duration : job_suspension Job)
    (j : Job) (R : Job → time) (t : time) (j_hi j_lo : Job) (HP : reduction.highest_priority_job_other_than_j job_arrival job_task arr_seq higher_eq_priority job_cost job_suspension_duration j R (reduction.sched_jitter job_arrival job_task arr_seq higher_eq_priority job_cost job_suspension_duration j R) t = some j_hi)
    (INlo : j_lo ∈ reduction.pending_jobs_other_than_j job_arrival job_task arr_seq higher_eq_priority job_cost job_suspension_duration j R (reduction.sched_jitter job_arrival job_task arr_seq higher_eq_priority job_cost job_suspension_duration j R) t) : higher_eq_priority (job_task j_hi) (job_task j_lo) = true := by
  apply seq_min_computes_min (FP_to_JLFP job_task higher_eq_priority)
    (fun y x z h1 h2 => H_priority_is_transitive (job_task y) (job_task x) (job_task z) h1 h2) _ _ j_hi j_lo HP INlo
  intro a b INa INb
  have Ta := H_jobs_from_taskset a (in_actual_arrivals_between_implies_arrived job_arrival _ arr_seq a 0 (t + 1)
    ((mem_pjo job_arrival job_task arr_seq higher_eq_priority job_cost job_suspension_duration j R _ t a).mp INa).1)
  have Tb := H_jobs_from_taskset b (in_actual_arrivals_between_implies_arrived job_arrival _ arr_seq b 0 (t + 1)
    ((mem_pjo job_arrival job_task arr_seq higher_eq_priority job_cost job_suspension_duration j R _ t b).mp INb).1)
  rcases H_priority_is_total (job_task a) (job_task b) Ta Tb with h | h
  · simp [FP_to_JLFP, h]
  · simp [FP_to_JLFP, h]

theorem sched_jitter_respects_policy {Task : Type u} [DecidableEq Task] {Job : Type v} [DecidableEq Job] (job_arrival : Job → time) (job_task : Job → Task) (ts : List Task) (arr_seq : arrival_sequence Job) (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq) (H_jobs_from_taskset : ∀ j, arrives_in arr_seq j → job_task j ∈ ts) (higher_eq_priority : FP_policy Task)
    (H_priority_is_reflexive : FP_is_reflexive higher_eq_priority) (H_priority_is_transitive : FP_is_transitive higher_eq_priority) (H_priority_is_total : FP_is_total_over_task_set higher_eq_priority ts) (job_cost : Job → time) (job_suspension_duration : job_suspension Job) (j : Job)
    (H_from_arrival_sequence : arrives_in arr_seq j) (R : Job → time) :
    jitter_aware.respects_FP_policy job_arrival (reduction.inflated_job_cost job_cost job_suspension_duration j) (reduction.job_jitter job_arrival job_task higher_eq_priority job_cost j R) job_task arr_seq (reduction.sched_jitter job_arrival job_task arr_seq higher_eq_priority job_cost job_suspension_duration j R) higher_eq_priority := by
  intro j1 j2 t IN BACK SCHED
  simp only [backlogged, Bool.and_eq_true] at BACK
  simp only [scheduled_at, decide_eq_true_eq] at SCHED
  rw [sched_jitter_uses_construction_function job_arrival job_task arr_seq higher_eq_priority job_cost job_suspension_duration j R] at SCHED
  have INlist : j1 ≠ j → j1 ∈ reduction.pending_jobs_other_than_j job_arrival job_task arr_seq higher_eq_priority job_cost job_suspension_duration j R (reduction.sched_jitter job_arrival job_task arr_seq higher_eq_priority job_cost job_suspension_duration j R) t := fun NEQ =>
    pending_in_pjo job_arrival job_task arr_seq H_arrival_times_are_consistent higher_eq_priority job_cost job_suspension_duration j R _ t j1 IN BACK.1 NEQ
  have ALL := hp_is_min job_arrival job_task ts arr_seq H_jobs_from_taskset higher_eq_priority H_priority_is_transitive
    H_priority_is_total job_cost job_suspension_duration j R t
  unfold reduction.build_schedule at SCHED
  split at SCHED
  · next PJ =>
    cases HP : reduction.highest_priority_job_other_than_j job_arrival job_task arr_seq higher_eq_priority job_cost job_suspension_duration j R (reduction.sched_jitter job_arrival job_task arr_seq higher_eq_priority job_cost job_suspension_duration j R) t with
    | none =>
      rw [HP] at SCHED; simp only [Option.some.injEq] at SCHED; subst SCHED
      by_cases EQ : j1 = j
      · subst EQ; exact H_priority_is_reflexive _
      · have EX := seq_min_exists (FP_to_JLFP job_task higher_eq_priority) _ j1 (INlist EQ)
        unfold reduction.highest_priority_job_other_than_j at HP
        rw [HP] at EX; simp at EX
    | some j_hp =>
      rw [HP] at SCHED; simp only at SCHED
      split at SCHED
      · next LP =>
        have E : j2 = j := (Option.some.inj SCHED).symm
        rw [E]
        by_cases EQ : j1 = j
        · rw [EQ]; exact H_priority_is_reflexive _
        · have INhp : j_hp ∈ reduction.pending_jobs_other_than_j job_arrival job_task arr_seq higher_eq_priority job_cost job_suspension_duration j R (reduction.sched_jitter job_arrival job_task arr_seq higher_eq_priority job_cost job_suspension_duration j R) t := seq_min_in_seq _ _ _ HP
          have ARRhp := in_actual_arrivals_between_implies_arrived job_arrival _ arr_seq j_hp 0 (t + 1)
            ((mem_pjo job_arrival job_task arr_seq higher_eq_priority job_cost job_suspension_duration j R _ t j_hp).mp INhp).1
          have NLP : higher_eq_priority (job_task j_hp) (job_task j) = false := by
            simpa [FP_to_JLFP] using LP
          have HPj : higher_eq_priority (job_task j) (job_task j_hp) = true := by
            rcases H_priority_is_total (job_task j) (job_task j_hp) (H_jobs_from_taskset j H_from_arrival_sequence)
              (H_jobs_from_taskset j_hp ARRhp) with h | h
            · exact h
            · rw [h] at NLP; exact absurd NLP (by simp)
          exact H_priority_is_transitive (job_task j_hp) (job_task j) (job_task j1) HPj (ALL j_hp j1 HP (INlist EQ))
      · next LP =>
        have E : j2 = j_hp := (Option.some.inj SCHED).symm
        rw [E]
        by_cases EQ : j1 = j
        · rw [EQ]; simpa [FP_to_JLFP] using LP
        · exact ALL j_hp j1 HP (INlist EQ)
  · next PJ =>
    by_cases EQ : j1 = j
    · subst EQ; exact absurd BACK.1 PJ
    · exact ALL j2 j1 SCHED (INlist EQ)

theorem sched_jitter_is_valid {Task : Type u} [DecidableEq Task] {Job : Type v} [DecidableEq Job] (job_arrival : Job → time) (job_task : Job → Task) (ts : List Task) (arr_seq : arrival_sequence Job) (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq) (H_jobs_from_taskset : ∀ j, arrives_in arr_seq j → job_task j ∈ ts) (higher_eq_priority : FP_policy Task)
    (H_priority_is_reflexive : FP_is_reflexive higher_eq_priority) (H_priority_is_transitive : FP_is_transitive higher_eq_priority) (H_priority_is_total : FP_is_total_over_task_set higher_eq_priority ts) (job_cost : Job → time) (job_suspension_duration : job_suspension Job) (sched_susp : schedule Job)
    (H_valid_schedule : valid_suspension_aware_schedule job_arrival arr_seq (FP_to_JLDP job_task higher_eq_priority)
      job_suspension_duration job_cost sched_susp)
    (j : Job) (H_from_arrival_sequence : arrives_in arr_seq j) (R : Job → time) :
    valid_jitter_aware_schedule job_arrival arr_seq (FP_to_JLDP job_task higher_eq_priority) (reduction.inflated_job_cost job_cost job_suspension_duration j) (reduction.job_jitter job_arrival job_task higher_eq_priority job_cost j R) (reduction.sched_jitter job_arrival job_task arr_seq higher_eq_priority job_cost job_suspension_duration j R) :=
  ⟨sched_jitter_jobs_come_from_arrival_sequence job_arrival job_task arr_seq higher_eq_priority job_cost
      job_suspension_duration sched_susp H_valid_schedule j H_from_arrival_sequence R,
    sched_jitter_jobs_execute_after_jitter job_arrival job_task arr_seq higher_eq_priority job_cost
      job_suspension_duration j H_from_arrival_sequence R,
    sched_jitter_completed_jobs_dont_execute job_arrival job_task arr_seq higher_eq_priority job_cost job_suspension_duration j R,
    sched_jitter_work_conserving job_arrival job_task arr_seq H_arrival_times_are_consistent higher_eq_priority
      job_cost job_suspension_duration j R,
    sched_jitter_respects_policy job_arrival job_task ts arr_seq H_arrival_times_are_consistent H_jobs_from_taskset
      higher_eq_priority H_priority_is_reflexive H_priority_is_transitive H_priority_is_total job_cost
      job_suspension_duration j H_from_arrival_sequence R⟩

theorem sched_jitter_does_not_pick_j {Task : Type u} [DecidableEq Task] {Job : Type v} [DecidableEq Job] (job_arrival : Job → time) (job_task : Job → Task) (ts : List Task) (arr_seq : arrival_sequence Job) (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq) (H_jobs_from_taskset : ∀ j, arrives_in arr_seq j → job_task j ∈ ts) (higher_eq_priority : FP_policy Task)
    (H_priority_is_transitive : FP_is_transitive higher_eq_priority) (H_priority_is_total : FP_is_total_over_task_set higher_eq_priority ts) (job_cost : Job → time) (job_suspension_duration : job_suspension Job) (j : Job) (R : Job → time) :
    ∀ (j_hp : Job) (t : time),
      arrives_in arr_seq j_hp →
      (!decide (j_hp = j)) = true →
      pending job_arrival (reduction.inflated_job_cost job_cost job_suspension_duration j) (reduction.job_jitter job_arrival job_task higher_eq_priority job_cost j R) (reduction.sched_jitter job_arrival job_task arr_seq higher_eq_priority job_cost job_suspension_duration j R) j_hp t = true →
      higher_eq_priority (job_task j_hp) (job_task j) = true →
      (!scheduled_at (reduction.sched_jitter job_arrival job_task arr_seq higher_eq_priority job_cost job_suspension_duration j R) j t) = true := by
  intro j_hp t ARRhp NEQ PENDhp HPhp
  simp only [Bool.not_eq_true', decide_eq_false_iff_not] at NEQ
  have INhp := pending_in_pjo job_arrival job_task arr_seq H_arrival_times_are_consistent higher_eq_priority job_cost job_suspension_duration j R _ t j_hp ARRhp PENDhp NEQ
  have ALL := hp_is_min job_arrival job_task ts arr_seq H_jobs_from_taskset higher_eq_priority H_priority_is_transitive
    H_priority_is_total job_cost job_suspension_duration j R t
  have NOTJ : ∀ y, y ∈ reduction.pending_jobs_other_than_j job_arrival job_task arr_seq higher_eq_priority job_cost job_suspension_duration j R (reduction.sched_jitter job_arrival job_task arr_seq higher_eq_priority job_cost job_suspension_duration j R) t → y ≠ j := fun y h => ((mem_pjo job_arrival job_task arr_seq higher_eq_priority job_cost job_suspension_duration j R _ t y).mp h).2.2
  simp only [Bool.not_eq_true', scheduled_at, decide_eq_false_iff_not]
  intro SCHEDj
  rw [sched_jitter_uses_construction_function job_arrival job_task arr_seq higher_eq_priority job_cost job_suspension_duration j R] at SCHEDj
  unfold reduction.build_schedule at SCHEDj
  split at SCHEDj
  · cases HP : reduction.highest_priority_job_other_than_j job_arrival job_task arr_seq higher_eq_priority job_cost job_suspension_duration j R (reduction.sched_jitter job_arrival job_task arr_seq higher_eq_priority job_cost job_suspension_duration j R) t with
    | none =>
      have EX := seq_min_exists (FP_to_JLFP job_task higher_eq_priority) _ j_hp INhp
      unfold reduction.highest_priority_job_other_than_j at HP
      rw [HP] at EX; simp at EX
    | some j_hp' =>
      rw [HP] at SCHEDj; simp only at SCHEDj
      split at SCHEDj
      · next LP =>
        have H1 := ALL j_hp' j_hp HP INhp
        have H2 := H_priority_is_transitive (job_task j_hp) (job_task j_hp') (job_task j) H1 HPhp
        simp [FP_to_JLFP, H2] at LP
      · simp only [Option.some.injEq] at SCHEDj
        exact NOTJ j_hp' (seq_min_in_seq _ _ _ HP) SCHEDj
  · exact NOTJ j (seq_min_in_seq _ _ _ SCHEDj) rfl

end Prosa.Classic.Analysis.Uni.Susp.Dynamic.Jitter.JitterScheduleProperties.JitterScheduleProperties
