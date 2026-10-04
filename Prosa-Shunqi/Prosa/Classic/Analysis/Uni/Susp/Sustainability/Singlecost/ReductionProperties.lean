-- Authoritative source:
-- ProsaBuddy classic Prosa (prosabuddy commit f692cb7479780cf6009493f373a309e13165201c)
-- source: classic/analysis/uni/susp/sustainability/singlecost/reduction_properties.v
-- sha256: see Prosa-Shunqi/classic-prosa/comprehensive-classic/file_order.csv (rank 133)

import Prosa.Classic.Util.All
import Prosa.Classic.Model.Priority
import Prosa.Classic.Model.Suspension
import Prosa.Classic.Model.Arrival.Basic.ArrivalSequence
import Prosa.Classic.Model.Schedule.Uni.ResponseTime
import Prosa.Classic.Model.Schedule.Uni.Susp.SuspensionIntervals
import Prosa.Classic.Model.Schedule.Uni.Susp.Schedule
import Prosa.Classic.Model.Schedule.Uni.Susp.Platform
import Prosa.Classic.Analysis.Uni.Susp.Sustainability.Singlecost.Reduction
import Prosa.Classic.Model.Schedule.Uni.Transformation.Construction

/-!
Properties of the single-cost-inflation reduction of a suspension-aware schedule
(Rocq module `SustainabilitySingleCostProperties`).

Representation notes:
* The Rocq alias `reduction := SustainabilitySingleCost` is a Lean namespace abbreviation of the accepted module.
* `~~ b` is `(!b) = true`; `x != y` in proposition position is `(!decide (x = y)) = true`.
* The section-local `Let`s (`arr_j`, `sched_susp_highercost`, `job_response_time_in_sched_susp_bounded_by`,
  `job_response_time_in_sched_susp_highercost_bounded_by`, `ready_jobs`, `hp_job`, `completed_in_sched_susp`,
  `completed_in_sched_susp_highercost`, `suspended_in_sched_susp`, `suspended_in_sched_susp_highercost`,
  `service_in_sched_susp`, `service_in_sched_susp_highercost`, `build_schedule`) are unfolded.
* Binder lists follow the Rocq contract.
-/

set_option linter.dupNamespace false
set_option linter.unusedVariables false

namespace Prosa.Classic.Analysis.Uni.Susp.Sustainability.Singlecost.ReductionProperties.SustainabilitySingleCostProperties

open Prosa.Classic.Model.Time.Time
open Prosa.Classic.Model.Arrival.Basic.ArrivalSequence.ArrivalSequence
open Prosa.Classic.Model.Priority.Priority
open Prosa.Classic.Model.Suspension.Suspension
open Prosa.Classic.Model.Schedule.Uni.Schedule.UniprocessorSchedule
open Prosa.Classic.Model.Schedule.Uni.Susp.LastExecution.LastExecution
open Prosa.Classic.Model.Schedule.Uni.Susp.SuspensionIntervals.SuspensionIntervals
open Prosa.Classic.Model.Schedule.Uni.Susp.Platform.PlatformWithSuspensions
open Prosa.Classic.Model.Schedule.Uni.ResponseTime.ResponseTime
open Prosa.Classic.Model.Schedule.Uni.Transformation.Construction.ScheduleConstruction
open Prosa.Classic.Util.Minmax (seq_min seq_min_in_seq seq_min_exists seq_min_computes_min)

namespace reduction
export Prosa.Classic.Analysis.Uni.Susp.Sustainability.Singlecost.Reduction.SustainabilitySingleCost
  (ready_jobs highest_priority_job build_schedule sched_susp_highercost)
end reduction

open reduction (sched_susp_highercost)

universe v

local macro "omega'" : tactic =>
  `(tactic| ((try dsimp only [Prosa.Classic.Model.Time.Time.time,
    Prosa.Classic.Model.Time.Time.instant, Prosa.Classic.Model.Time.Time.duration] at *) <;>
    omega))

/-! ### Proof-local facts -/

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

/-- LEAN_HELPER: whether an arrived job is suspended at `k` only depends on its completion status and the schedule
before `k`. -/
private theorem suspended_congr {Job : Type v} [DecidableEq Job] (job_arrival c1 c2 : Job → time) (ns : job_suspension Job)
    (s1 s2 : schedule Job) (x : Job) (k : time) (ARR : has_arrived job_arrival x k = true)
    (H : ∀ i, i < k → scheduled_at s1 x i = scheduled_at s2 x i)
    (COMP : completed_by c1 s1 x k = completed_by c2 s2 x k) :
    suspended_at job_arrival c1 ns s1 x k = suspended_at job_arrival c2 ns s2 x k := by
  have TALE := tale_congr job_arrival s1 s2 x k H
  have LE := last_execution_bounded_by_identity job_arrival s2 x k ARR
  have SERV : service s1 x (time_after_last_execution job_arrival s2 x k) =
      service s2 x (time_after_last_execution job_arrival s2 x k) :=
    service_congr s1 s2 x _ (fun i hi => H i (by omega'))
  unfold suspended_at suspension_duration
  rw [COMP, TALE, SERV]

/-- LEAN_HELPER: a job of `jobs_arrived_up_to arr_seq t` has arrived by `t`. -/
private theorem arrived_of_mem_up_to {Job : Type v} [DecidableEq Job] (job_arrival : Job → time) (arr_seq : arrival_sequence Job)
    (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq) (x : Job) (t : time)
    (IN : x ∈ jobs_arrived_up_to arr_seq t) : has_arrived job_arrival x t = true := by
  have := in_arrivals_implies_arrived_before job_arrival arr_seq H_arrival_times_are_consistent x (t + 1) IN
  simp only [arrived_before, has_arrived, decide_eq_true_eq] at this ⊢
  omega'

/-! ### Properties of the schedule construction -/

theorem sched_susp_highercost_depends_only_on_prefix {Job : Type v} [DecidableEq Job] (job_arrival : Job → time) (arr_seq : arrival_sequence Job)
    (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq)
    (higher_eq_priority : JLDP_policy Job) (sched_susp : schedule Job) (job_suspension_duration : job_suspension Job)
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched_susp)
    (inflated_job_cost : Job → time) :
    ∀ (sched1 sched2 : schedule Job) (t : Nat), (∀ t0, t0 < t → sched1 t0 = sched2 t0) →
      reduction.build_schedule job_arrival arr_seq higher_eq_priority sched_susp job_suspension_duration inflated_job_cost sched1 t = reduction.build_schedule job_arrival arr_seq higher_eq_priority sched_susp job_suspension_duration inflated_job_cost sched2 t := by
  intro sched1 sched2 t ALL
  have SCH : ∀ x i, i < t → scheduled_at sched1 x i = scheduled_at sched2 x i := by
    intro x i hi; simp only [scheduled_at, ALL i hi]
  have COMP : ∀ x, completed_by inflated_job_cost sched1 x t = completed_by inflated_job_cost sched2 x t := by
    intro x; simp only [completed_by, service_congr sched1 sched2 x t (SCH x)]
  have PEND : ∀ x, pending job_arrival inflated_job_cost sched1 x t =
      pending job_arrival inflated_job_cost sched2 x t := by
    intro x; simp only [pending, COMP]
  have SUSP : ∀ x, has_arrived job_arrival x t = true →
      suspended_at job_arrival inflated_job_cost job_suspension_duration sched1 x t = suspended_at job_arrival inflated_job_cost job_suspension_duration sched2 x t :=
    fun x ARR => suspended_congr job_arrival _ _ _ sched1 sched2 x t ARR (SCH x) (COMP x)
  have READY : reduction.ready_jobs job_arrival arr_seq job_suspension_duration inflated_job_cost sched1 t = reduction.ready_jobs job_arrival arr_seq job_suspension_duration inflated_job_cost sched2 t := by
    unfold reduction.ready_jobs
    apply List.filter_congr
    intro x IN
    rw [PEND x, SUSP x (arrived_of_mem_up_to job_arrival arr_seq H_arrival_times_are_consistent x t IN)]
  unfold reduction.build_schedule reduction.highest_priority_job
  rw [READY]
  cases seq_min (higher_eq_priority t) (reduction.ready_jobs job_arrival arr_seq job_suspension_duration inflated_job_cost sched2 t) with
  | none => rfl
  | some j_hp =>
    simp only
    cases SS : sched_susp t with
    | none => rfl
    | some j_s =>
      simp only
      have ARR := H_jobs_must_arrive_to_execute j_s t (by simp [scheduled_at, SS])
      rw [PEND j_s, SUSP j_s ARR]

theorem sched_susp_highercost_uses_construction_function {Job : Type v} [DecidableEq Job] (job_arrival : Job → time) (arr_seq : arrival_sequence Job)
    (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq)
    (higher_eq_priority : JLDP_policy Job) (sched_susp : schedule Job) (job_suspension_duration : job_suspension Job)
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched_susp)
    (inflated_job_cost : Job → time) :
    ∀ t, (sched_susp_highercost job_arrival arr_seq higher_eq_priority sched_susp job_suspension_duration inflated_job_cost) t = reduction.build_schedule job_arrival arr_seq higher_eq_priority sched_susp job_suspension_duration inflated_job_cost (sched_susp_highercost job_arrival arr_seq higher_eq_priority sched_susp job_suspension_duration inflated_job_cost) t := by
  intro t
  exact prefix_dependent_schedule_construction _ _
    (sched_susp_highercost_depends_only_on_prefix job_arrival arr_seq H_arrival_times_are_consistent higher_eq_priority sched_susp job_suspension_duration H_jobs_must_arrive_to_execute inflated_job_cost) t

/-- LEAN_HELPER: a job scheduled in the new schedule is pending and not suspended there, and either it is one of
the ready jobs or it is scheduled in `sched_susp`. -/
private theorem scheduled_facts {Job : Type v} [DecidableEq Job] (job_arrival : Job → time) (arr_seq : arrival_sequence Job)
    (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq)
    (higher_eq_priority : JLDP_policy Job) (sched_susp : schedule Job) (job_suspension_duration : job_suspension Job)
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched_susp)
    (inflated_job_cost : Job → time) (x : Job) (t : time)
    (SCHED : scheduled_at (sched_susp_highercost job_arrival arr_seq higher_eq_priority sched_susp job_suspension_duration inflated_job_cost) x t = true) :
    pending job_arrival inflated_job_cost (sched_susp_highercost job_arrival arr_seq higher_eq_priority sched_susp job_suspension_duration inflated_job_cost) x t = true ∧ (!suspended_at job_arrival inflated_job_cost job_suspension_duration (sched_susp_highercost job_arrival arr_seq higher_eq_priority sched_susp job_suspension_duration inflated_job_cost) x t) = true ∧
      (x ∈ reduction.ready_jobs job_arrival arr_seq job_suspension_duration inflated_job_cost (sched_susp_highercost job_arrival arr_seq higher_eq_priority sched_susp job_suspension_duration inflated_job_cost) t ∨ sched_susp t = some x) := by
  simp only [scheduled_at, decide_eq_true_eq] at SCHED
  rw [sched_susp_highercost_uses_construction_function job_arrival arr_seq H_arrival_times_are_consistent higher_eq_priority sched_susp job_suspension_duration H_jobs_must_arrive_to_execute inflated_job_cost] at SCHED
  have INR : ∀ y, y ∈ reduction.ready_jobs job_arrival arr_seq job_suspension_duration inflated_job_cost (sched_susp_highercost job_arrival arr_seq higher_eq_priority sched_susp job_suspension_duration inflated_job_cost) t → pending job_arrival inflated_job_cost (sched_susp_highercost job_arrival arr_seq higher_eq_priority sched_susp job_suspension_duration inflated_job_cost) y t = true ∧
      (!suspended_at job_arrival inflated_job_cost job_suspension_duration (sched_susp_highercost job_arrival arr_seq higher_eq_priority sched_susp job_suspension_duration inflated_job_cost) y t) = true := by
    intro y IN
    unfold reduction.ready_jobs at IN
    have := (List.mem_filter.mp IN).2
    simpa only [Bool.and_eq_true] using this
  unfold reduction.build_schedule at SCHED
  cases HP : reduction.highest_priority_job job_arrival arr_seq higher_eq_priority job_suspension_duration inflated_job_cost (sched_susp_highercost job_arrival arr_seq higher_eq_priority sched_susp job_suspension_duration inflated_job_cost) t with
  | none => rw [HP] at SCHED; simp at SCHED
  | some j_hp =>
    have INhp : j_hp ∈ reduction.ready_jobs job_arrival arr_seq job_suspension_duration inflated_job_cost (sched_susp_highercost job_arrival arr_seq higher_eq_priority sched_susp job_suspension_duration inflated_job_cost) t := seq_min_in_seq _ _ _ HP
    rw [HP] at SCHED
    simp only at SCHED
    cases SS : sched_susp t with
    | none =>
      rw [SS] at SCHED; simp only [Option.some.injEq] at SCHED; subst SCHED
      exact ⟨(INR _ INhp).1, (INR _ INhp).2, Or.inl INhp⟩
    | some j_s =>
      rw [SS] at SCHED; simp only at SCHED
      split at SCHED
      · next COND =>
        simp only [Option.some.injEq] at SCHED; subst SCHED
        simp only [Bool.and_eq_true] at COND
        exact ⟨COND.1.1, COND.1.2, Or.inr rfl⟩
      · simp only [Option.some.injEq] at SCHED; subst SCHED
        exact ⟨(INR _ INhp).1, (INR _ INhp).2, Or.inl INhp⟩

/-! ### Basic properties of the generated schedule -/

theorem sched_susp_highercost_jobs_come_from_arrival_sequence {Job : Type v} [DecidableEq Job] (job_arrival : Job → time) (arr_seq : arrival_sequence Job)
    (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq)
    (higher_eq_priority : JLDP_policy Job) (sched_susp : schedule Job)
    (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched_susp arr_seq)
    (job_suspension_duration : job_suspension Job)
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched_susp)
    (inflated_job_cost : Job → time) :
    jobs_come_from_arrival_sequence (sched_susp_highercost job_arrival arr_seq higher_eq_priority sched_susp job_suspension_duration inflated_job_cost) arr_seq := by
  intro x t SCHED
  rcases (scheduled_facts job_arrival arr_seq H_arrival_times_are_consistent higher_eq_priority sched_susp job_suspension_duration H_jobs_must_arrive_to_execute inflated_job_cost x t SCHED).2.2 with IN | SS
  · unfold reduction.ready_jobs at IN
    exact in_arrivals_implies_arrived arr_seq x 0 (t + 1) (List.mem_filter.mp IN).1
  · exact H_jobs_come_from_arrival_sequence x t (by simp [scheduled_at, SS])

theorem sched_susp_highercost_jobs_must_arrive_to_execute {Job : Type v} [DecidableEq Job] (job_arrival : Job → time) (arr_seq : arrival_sequence Job)
    (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq)
    (higher_eq_priority : JLDP_policy Job) (sched_susp : schedule Job) (job_suspension_duration : job_suspension Job)
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched_susp)
    (inflated_job_cost : Job → time) :
    jobs_must_arrive_to_execute job_arrival (sched_susp_highercost job_arrival arr_seq higher_eq_priority sched_susp job_suspension_duration inflated_job_cost) := by
  intro x t SCHED
  have PEND := (scheduled_facts job_arrival arr_seq H_arrival_times_are_consistent higher_eq_priority sched_susp job_suspension_duration H_jobs_must_arrive_to_execute inflated_job_cost x t SCHED).1
  simp only [pending, Bool.and_eq_true] at PEND
  exact PEND.1

theorem sched_susp_highercost_completed_jobs_dont_execute {Job : Type v} [DecidableEq Job] (job_arrival : Job → time) (arr_seq : arrival_sequence Job)
    (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq)
    (higher_eq_priority : JLDP_policy Job) (sched_susp : schedule Job) (job_suspension_duration : job_suspension Job)
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched_susp)
    (inflated_job_cost : Job → time) :
    completed_jobs_dont_execute inflated_job_cost (sched_susp_highercost job_arrival arr_seq higher_eq_priority sched_susp job_suspension_duration inflated_job_cost) := by
  intro x t
  induction t with
  | zero => simp [service, service_during]
  | succ t IHt =>
    have STEP : service (sched_susp_highercost job_arrival arr_seq higher_eq_priority sched_susp job_suspension_duration inflated_job_cost) x (t + 1) = service (sched_susp_highercost job_arrival arr_seq higher_eq_priority sched_susp job_suspension_duration inflated_job_cost) x t + service_at (sched_susp_highercost job_arrival arr_seq higher_eq_priority sched_susp job_suspension_duration inflated_job_cost) x t := by
      unfold service service_during
      rw [Finset.sum_Ico_succ_top (Nat.zero_le _)]
    rw [STEP]
    rcases Nat.lt_or_ge (service (sched_susp_highercost job_arrival arr_seq higher_eq_priority sched_susp job_suspension_duration inflated_job_cost) x t) (inflated_job_cost x) with LT | GE
    · have : service_at (sched_susp_highercost job_arrival arr_seq higher_eq_priority sched_susp job_suspension_duration inflated_job_cost) x t ≤ 1 := by
        unfold service_at; cases scheduled_at _ x t <;> simp
      omega'
    · have NS : scheduled_at (sched_susp_highercost job_arrival arr_seq higher_eq_priority sched_susp job_suspension_duration inflated_job_cost) x t = false := by
        cases hs : scheduled_at (sched_susp_highercost job_arrival arr_seq higher_eq_priority sched_susp job_suspension_duration inflated_job_cost) x t
        · rfl
        · have PEND := (scheduled_facts job_arrival arr_seq H_arrival_times_are_consistent higher_eq_priority sched_susp job_suspension_duration H_jobs_must_arrive_to_execute inflated_job_cost x t hs).1
          simp only [pending, completed_by, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at PEND
          exact absurd GE PEND.2
      simp only [service_at, NS, Bool.toNat_false, Nat.add_zero]
      exact IHt

/-- LEAN_HELPER: a backlogged job of the arrival sequence is one of the ready jobs. -/
private theorem backlogged_in_ready_jobs {Job : Type v} [DecidableEq Job] (job_arrival : Job → time) (arr_seq : arrival_sequence Job)
    (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq)
    (job_suspension_duration : job_suspension Job) (inflated_job_cost : Job → time) (sched : schedule Job)
    (x : Job) (t : time) (IN : arrives_in arr_seq x)
    (PEND : pending job_arrival inflated_job_cost sched x t = true)
    (NOTSUSP : (!suspended_at job_arrival inflated_job_cost job_suspension_duration sched x t) = true) : x ∈ reduction.ready_jobs job_arrival arr_seq job_suspension_duration inflated_job_cost sched t := by
  unfold reduction.ready_jobs
  rw [List.mem_filter]
  refine ⟨?_, by simp only [PEND, NOTSUSP, Bool.and_self]⟩
  have ARR := PEND
  simp only [pending, has_arrived, Bool.and_eq_true, decide_eq_true_eq] at ARR
  exact arrived_between_implies_in_arrivals job_arrival arr_seq H_arrival_times_are_consistent x 0 (t + 1) IN
    (by simp only [arrived_between, Bool.and_eq_true, decide_eq_true_eq]; omega')

theorem sched_susp_highercost_work_conserving {Job : Type v} [DecidableEq Job] (job_arrival : Job → time) (arr_seq : arrival_sequence Job)
    (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq)
    (higher_eq_priority : JLDP_policy Job) (sched_susp : schedule Job) (job_suspension_duration : job_suspension Job)
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched_susp)
    (inflated_job_cost : Job → time) :
    work_conserving job_arrival inflated_job_cost job_suspension_duration arr_seq (sched_susp_highercost job_arrival arr_seq higher_eq_priority sched_susp job_suspension_duration inflated_job_cost) := by
  intro x t IN BACK
  simp only [Prosa.Classic.Model.Schedule.Uni.Susp.Schedule.ScheduleWithSuspensions.backlogged,
    Bool.and_eq_true] at BACK
  have INR := backlogged_in_ready_jobs job_arrival arr_seq H_arrival_times_are_consistent job_suspension_duration
    inflated_job_cost _ x t IN BACK.1.1 BACK.2
  have EX := seq_min_exists (higher_eq_priority t) _ x INR
  simp only [scheduled_at, decide_eq_true_eq]
  rw [sched_susp_highercost_uses_construction_function job_arrival arr_seq H_arrival_times_are_consistent higher_eq_priority sched_susp job_suspension_duration H_jobs_must_arrive_to_execute inflated_job_cost]
  unfold reduction.build_schedule
  cases HP : reduction.highest_priority_job job_arrival arr_seq higher_eq_priority job_suspension_duration inflated_job_cost (sched_susp_highercost job_arrival arr_seq higher_eq_priority sched_susp job_suspension_duration inflated_job_cost) t with
  | none =>
    unfold reduction.highest_priority_job at HP
    rw [HP] at EX; simp at EX
  | some j_hp =>
    simp only
    cases sched_susp t with
    | none => exact ⟨j_hp, rfl⟩
    | some j_s =>
      simp only
      split
      · exact ⟨j_s, rfl⟩
      · exact ⟨j_hp, rfl⟩

theorem sched_susp_highercost_respects_policy {Job : Type v} [DecidableEq Job] (job_arrival : Job → time) (arr_seq : arrival_sequence Job)
    (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq)
    (higher_eq_priority : JLDP_policy Job) (H_priority_is_transitive : JLDP_is_transitive higher_eq_priority)
    (H_priority_is_total : JLDP_is_total arr_seq higher_eq_priority) (sched_susp : schedule Job) (job_suspension_duration : job_suspension Job)
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched_susp)
    (inflated_job_cost : Job → time) :
    respects_JLDP_policy job_arrival inflated_job_cost job_suspension_duration arr_seq (sched_susp_highercost job_arrival arr_seq higher_eq_priority sched_susp job_suspension_duration inflated_job_cost) higher_eq_priority := by
  intro x j2 t IN BACK SCHED
  simp only [Prosa.Classic.Model.Schedule.Uni.Susp.Schedule.ScheduleWithSuspensions.backlogged,
    Bool.and_eq_true] at BACK
  have INR := backlogged_in_ready_jobs job_arrival arr_seq H_arrival_times_are_consistent job_suspension_duration
    inflated_job_cost _ x t IN BACK.1.1 BACK.2
  simp only [scheduled_at, decide_eq_true_eq] at SCHED
  rw [sched_susp_highercost_uses_construction_function job_arrival arr_seq H_arrival_times_are_consistent higher_eq_priority sched_susp job_suspension_duration H_jobs_must_arrive_to_execute inflated_job_cost] at SCHED
  unfold reduction.build_schedule at SCHED
  cases HP : reduction.highest_priority_job job_arrival arr_seq higher_eq_priority job_suspension_duration inflated_job_cost (sched_susp_highercost job_arrival arr_seq higher_eq_priority sched_susp job_suspension_duration inflated_job_cost) t with
  | none => rw [HP] at SCHED; simp at SCHED
  | some j_min =>
    have ALL : ∀ y, y ∈ reduction.ready_jobs job_arrival arr_seq job_suspension_duration inflated_job_cost (sched_susp_highercost job_arrival arr_seq higher_eq_priority sched_susp job_suspension_duration inflated_job_cost) t → higher_eq_priority t j_min y = true := by
      intro y INy
      apply seq_min_computes_min (higher_eq_priority t) (H_priority_is_transitive t) _ _ j_min y HP INy
      intro a b INa INb
      unfold reduction.ready_jobs at INa INb
      exact H_priority_is_total a b t (in_arrivals_implies_arrived arr_seq a 0 (t + 1) (List.mem_filter.mp INa).1)
        (in_arrivals_implies_arrived arr_seq b 0 (t + 1) (List.mem_filter.mp INb).1)
    rw [HP] at SCHED
    simp only at SCHED
    cases SS : sched_susp t with
    | none =>
      rw [SS] at SCHED; simp only at SCHED
      rw [← Option.some.inj SCHED]; exact ALL x INR
    | some j_s =>
      rw [SS] at SCHED; simp only at SCHED
      split at SCHED
      · next COND =>
        rw [← Option.some.inj SCHED]
        simp only [Bool.and_eq_true] at COND
        exact H_priority_is_transitive t j_min j_s x COND.2 (ALL x INR)
      · rw [← Option.some.inj SCHED]; exact ALL x INR

theorem sched_susp_highercost_respects_self_suspensions {Job : Type v} [DecidableEq Job] (job_arrival : Job → time) (arr_seq : arrival_sequence Job)
    (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq)
    (higher_eq_priority : JLDP_policy Job) (sched_susp : schedule Job) (job_suspension_duration : job_suspension Job)
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched_susp)
    (inflated_job_cost : Job → time) :
    respects_self_suspensions job_arrival inflated_job_cost job_suspension_duration (sched_susp_highercost job_arrival arr_seq higher_eq_priority sched_susp job_suspension_duration inflated_job_cost) := by
  intro x t SCHED SUSP
  have NOTSUSP := (scheduled_facts job_arrival arr_seq H_arrival_times_are_consistent higher_eq_priority sched_susp job_suspension_duration H_jobs_must_arrive_to_execute inflated_job_cost x t SCHED).2.1
  rw [SUSP] at NOTSUSP; exact absurd NOTSUSP (by simp)

/-! ### Scheduling invariant -/

theorem sched_susp_highercost_same_completion {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time) (arr_seq : arrival_sequence Job)
    (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq)
    (higher_eq_priority : JLDP_policy Job) (sched_susp : schedule Job) (job_suspension_duration : job_suspension Job)
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched_susp)
    (j : Job) (inflated_job_cost : Job → time) (H_cost_of_j_does_not_decrease : job_cost j ≤ inflated_job_cost j)
    (H_inflation_only_for_job_j : ∀ any_j, (!decide (any_j = j)) = true → inflated_job_cost any_j = job_cost any_j)
    (t : time) (H_j_has_not_completed : (!completed_by job_cost sched_susp j t) = true)
    (H_schedules_are_the_same : ∀ k any_j, k < t →
      scheduled_at sched_susp any_j k = scheduled_at (sched_susp_highercost job_arrival arr_seq higher_eq_priority sched_susp job_suspension_duration inflated_job_cost) any_j k)
    (k : time) (H_k_before_t : k ≤ t) :
    ∀ any_j, completed_by job_cost sched_susp any_j k = completed_by inflated_job_cost (sched_susp_highercost job_arrival arr_seq higher_eq_priority sched_susp job_suspension_duration inflated_job_cost) any_j k := by
  intro any_j
  have SERV : service sched_susp any_j k = service (sched_susp_highercost job_arrival arr_seq higher_eq_priority sched_susp job_suspension_duration inflated_job_cost) any_j k :=
    service_congr _ _ any_j k (fun i hi => H_schedules_are_the_same i any_j (by omega'))
  by_cases EQ : any_j = j
  · subst EQ
    have NC : ¬ job_cost any_j ≤ service sched_susp any_j t := by
      simpa [completed_by] using H_j_has_not_completed
    have MONO : service sched_susp any_j k ≤ service sched_susp any_j t := by
      unfold service service_during
      exact Finset.sum_le_sum_of_subset (Finset.Ico_subset_Ico (Nat.le_refl 0) H_k_before_t)
    have C1 : completed_by job_cost sched_susp any_j k = false := by
      simp only [completed_by, decide_eq_false_iff_not]; omega'
    have C2 : completed_by inflated_job_cost (sched_susp_highercost job_arrival arr_seq higher_eq_priority sched_susp job_suspension_duration inflated_job_cost) any_j k = false := by
      simp only [completed_by, decide_eq_false_iff_not]; rw [← SERV]; omega'
    rw [C1, C2]
  · have E := H_inflation_only_for_job_j any_j (by simp [EQ])
    simp only [completed_by, E, SERV]

theorem sched_susp_highercost_same_time_after_last_exec {Job : Type v} [DecidableEq Job] (job_arrival : Job → time)
    (arr_seq : arrival_sequence Job) (higher_eq_priority : JLDP_policy Job) (sched_susp : schedule Job)
    (job_suspension_duration : job_suspension Job) (inflated_job_cost : Job → time) (t : time)
    (H_schedules_are_the_same : ∀ k any_j, k < t →
      scheduled_at sched_susp any_j k = scheduled_at (sched_susp_highercost job_arrival arr_seq higher_eq_priority sched_susp job_suspension_duration inflated_job_cost) any_j k)
    (k : time) (H_k_before_t : k ≤ t) :
    ∀ any_j, time_after_last_execution job_arrival sched_susp any_j k =
      time_after_last_execution job_arrival (sched_susp_highercost job_arrival arr_seq higher_eq_priority sched_susp job_suspension_duration inflated_job_cost) any_j k := by
  intro any_j
  exact tale_congr job_arrival _ _ any_j k (fun i hi => H_schedules_are_the_same i any_j (by omega'))

theorem sched_susp_highercost_same_suspension_duration {Job : Type v} [DecidableEq Job] (job_arrival : Job → time)
    (arr_seq : arrival_sequence Job) (higher_eq_priority : JLDP_policy Job) (sched_susp : schedule Job)
    (job_suspension_duration : job_suspension Job) (inflated_job_cost : Job → time) (t : time)
    (H_schedules_are_the_same : ∀ k any_j, k < t →
      scheduled_at sched_susp any_j k = scheduled_at (sched_susp_highercost job_arrival arr_seq higher_eq_priority sched_susp job_suspension_duration inflated_job_cost) any_j k)
    (k : time) (H_k_before_t : k ≤ t) :
    ∀ any_j, has_arrived job_arrival any_j k = true →
      suspension_duration job_arrival job_suspension_duration sched_susp any_j k =
        suspension_duration job_arrival job_suspension_duration (sched_susp_highercost job_arrival arr_seq higher_eq_priority sched_susp job_suspension_duration inflated_job_cost) any_j k := by
  intro any_j ARR
  have SCH : ∀ i, i < k → scheduled_at sched_susp any_j i = scheduled_at (sched_susp_highercost job_arrival arr_seq higher_eq_priority sched_susp job_suspension_duration inflated_job_cost) any_j i :=
    fun i hi => H_schedules_are_the_same i any_j (by omega')
  have TALE := tale_congr job_arrival _ _ any_j k SCH
  have LE := last_execution_bounded_by_identity job_arrival (sched_susp_highercost job_arrival arr_seq higher_eq_priority sched_susp job_suspension_duration inflated_job_cost) any_j k ARR
  unfold suspension_duration
  rw [TALE, service_congr _ _ any_j _ (fun i hi => SCH i (by omega'))]

theorem sched_susp_highercost_same_suspension {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time) (arr_seq : arrival_sequence Job)
    (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq)
    (higher_eq_priority : JLDP_policy Job) (sched_susp : schedule Job) (job_suspension_duration : job_suspension Job)
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched_susp)
    (j : Job) (inflated_job_cost : Job → time) (H_cost_of_j_does_not_decrease : job_cost j ≤ inflated_job_cost j)
    (H_inflation_only_for_job_j : ∀ any_j, (!decide (any_j = j)) = true → inflated_job_cost any_j = job_cost any_j)
    (t : time) (H_j_has_not_completed : (!completed_by job_cost sched_susp j t) = true)
    (H_schedules_are_the_same : ∀ k any_j, k < t →
      scheduled_at sched_susp any_j k = scheduled_at (sched_susp_highercost job_arrival arr_seq higher_eq_priority sched_susp job_suspension_duration inflated_job_cost) any_j k)
    (k : time) (H_k_before_t : k ≤ t) :
    ∀ any_j, has_arrived job_arrival any_j k = true →
      suspended_at job_arrival job_cost job_suspension_duration sched_susp any_j k = suspended_at job_arrival inflated_job_cost job_suspension_duration (sched_susp_highercost job_arrival arr_seq higher_eq_priority sched_susp job_suspension_duration inflated_job_cost) any_j k := by
  intro any_j ARR
  exact suspended_congr job_arrival _ _ _ _ _ any_j k ARR
    (fun i hi => H_schedules_are_the_same i any_j (by omega'))
    (sched_susp_highercost_same_completion job_arrival job_cost arr_seq H_arrival_times_are_consistent higher_eq_priority sched_susp job_suspension_duration H_jobs_must_arrive_to_execute j inflated_job_cost H_cost_of_j_does_not_decrease H_inflation_only_for_job_j t H_j_has_not_completed H_schedules_are_the_same k H_k_before_t
      any_j)

theorem sched_susp_highercost_same_schedule {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time) (arr_seq : arrival_sequence Job)
    (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq)
    (higher_eq_priority : JLDP_policy Job) (H_priority_is_reflexive : JLDP_is_reflexive higher_eq_priority)
    (sched_susp : schedule Job) (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched_susp arr_seq)
    (job_suspension_duration : job_suspension Job)
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched_susp)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched_susp)
    (H_work_conserving : work_conserving job_arrival job_cost job_suspension_duration arr_seq sched_susp)
    (H_respects_priority :
      respects_JLDP_policy job_arrival job_cost job_suspension_duration arr_seq sched_susp higher_eq_priority)
    (H_respects_self_suspensions : respects_self_suspensions job_arrival job_cost job_suspension_duration sched_susp)
    (j : Job) (inflated_job_cost : Job → time) (H_cost_of_j_does_not_decrease : job_cost j ≤ inflated_job_cost j)
    (H_inflation_only_for_job_j : ∀ any_j, (!decide (any_j = j)) = true → inflated_job_cost any_j = job_cost any_j)
    (t : time) (H_j_has_not_completed : (!completed_by job_cost sched_susp j t) = true)
    (H_schedules_are_the_same : ∀ k any_j, k < t →
      scheduled_at sched_susp any_j k = scheduled_at (sched_susp_highercost job_arrival arr_seq higher_eq_priority sched_susp job_suspension_duration inflated_job_cost) any_j k)
    (k : time) (H_k_before_t : k ≤ t) :
    ∀ any_j, scheduled_at sched_susp any_j k = scheduled_at (sched_susp_highercost job_arrival arr_seq higher_eq_priority sched_susp job_suspension_duration inflated_job_cost) any_j k := by
  have LEMMAcomp := sched_susp_highercost_same_completion job_arrival job_cost arr_seq H_arrival_times_are_consistent higher_eq_priority sched_susp job_suspension_duration H_jobs_must_arrive_to_execute j inflated_job_cost H_cost_of_j_does_not_decrease H_inflation_only_for_job_j t H_j_has_not_completed H_schedules_are_the_same
    k H_k_before_t
  have LEMMAsusp := sched_susp_highercost_same_suspension job_arrival job_cost arr_seq H_arrival_times_are_consistent higher_eq_priority sched_susp job_suspension_duration H_jobs_must_arrive_to_execute j inflated_job_cost H_cost_of_j_does_not_decrease H_inflation_only_for_job_j t H_j_has_not_completed H_schedules_are_the_same
    k H_k_before_t
  -- facts about a job scheduled in `sched_susp` at time `k`
  have SFACTS : ∀ j_s, sched_susp k = some j_s →
      has_arrived job_arrival j_s k = true ∧ arrives_in arr_seq j_s ∧
      pending job_arrival inflated_job_cost (sched_susp_highercost job_arrival arr_seq higher_eq_priority sched_susp job_suspension_duration inflated_job_cost) j_s k = true ∧ (!suspended_at job_arrival inflated_job_cost job_suspension_duration (sched_susp_highercost job_arrival arr_seq higher_eq_priority sched_susp job_suspension_duration inflated_job_cost) j_s k) = true := by
    intro j_s SS
    have SCHs : scheduled_at sched_susp j_s k = true := by simp [scheduled_at, SS]
    have ARR := H_jobs_must_arrive_to_execute j_s k SCHs
    have NOTCOMPs := completed_implies_not_scheduled job_cost sched_susp j_s H_completed_jobs_dont_execute k
    have NC : completed_by job_cost sched_susp j_s k = false := by
      cases h : completed_by job_cost sched_susp j_s k
      · rfl
      · have := NOTCOMPs h; rw [SCHs] at this; exact absurd this (by simp)
    have NS : suspended_at job_arrival job_cost job_suspension_duration sched_susp j_s k = false := by
      cases h : suspended_at job_arrival job_cost job_suspension_duration sched_susp j_s k
      · rfl
      · exact absurd h (H_respects_self_suspensions j_s k SCHs)
    refine ⟨ARR, H_jobs_come_from_arrival_sequence j_s k SCHs, ?_, ?_⟩
    · simp only [pending, ARR, Bool.true_and, ← LEMMAcomp j_s, NC, Bool.not_false]
    · rw [← LEMMAsusp j_s ARR, NS]; rfl
  suffices EQsched : sched_susp k = (sched_susp_highercost job_arrival arr_seq higher_eq_priority sched_susp job_suspension_duration inflated_job_cost) k by
    intro any_j; simp only [scheduled_at, EQsched]
  rw [sched_susp_highercost_uses_construction_function job_arrival arr_seq H_arrival_times_are_consistent higher_eq_priority sched_susp job_suspension_duration H_jobs_must_arrive_to_execute inflated_job_cost]
  unfold reduction.build_schedule
  cases HP : reduction.highest_priority_job job_arrival arr_seq higher_eq_priority job_suspension_duration inflated_job_cost (sched_susp_highercost job_arrival arr_seq higher_eq_priority sched_susp job_suspension_duration inflated_job_cost) k with
  | none =>
    simp only
    cases SS : sched_susp k with
    | none => rfl
    | some j_s =>
      exfalso
      obtain ⟨ARR, INs, PENDw, NSw⟩ := SFACTS j_s SS
      have INR := backlogged_in_ready_jobs job_arrival arr_seq H_arrival_times_are_consistent job_suspension_duration
        inflated_job_cost _ j_s k INs PENDw NSw
      have EX := seq_min_exists (higher_eq_priority k) _ j_s INR
      unfold reduction.highest_priority_job at HP
      rw [HP] at EX; simp at EX
  | some j_hp =>
    simp only
    have INhp : j_hp ∈ reduction.ready_jobs job_arrival arr_seq job_suspension_duration inflated_job_cost (sched_susp_highercost job_arrival arr_seq higher_eq_priority sched_susp job_suspension_duration inflated_job_cost) k := seq_min_in_seq _ _ _ HP
    unfold reduction.ready_jobs at INhp
    rw [List.mem_filter] at INhp
    obtain ⟨INarr, PROP⟩ := INhp
    simp only [Bool.and_eq_true] at PROP
    obtain ⟨PENDhp, NOTSUSPhp⟩ := PROP
    have ARRINhp : arrives_in arr_seq j_hp := in_arrivals_implies_arrived arr_seq j_hp 0 (k + 1) INarr
    have ARRhp := arrived_of_mem_up_to job_arrival arr_seq H_arrival_times_are_consistent j_hp k INarr
    have NOTCOMPhp : (!completed_by job_cost sched_susp j_hp k) = true := by
      simp only [pending, Bool.and_eq_true] at PENDhp
      rw [LEMMAcomp j_hp]; exact PENDhp.2
    have NOTSUSPs : (!suspended_at job_arrival job_cost job_suspension_duration sched_susp j_hp k) = true := by
      rw [LEMMAsusp j_hp ARRhp]; exact NOTSUSPhp
    cases SS : sched_susp k with
    | none =>
      exfalso
      have BACK : Prosa.Classic.Model.Schedule.Uni.Susp.Schedule.ScheduleWithSuspensions.backlogged job_arrival
          job_cost job_suspension_duration sched_susp j_hp k = true := by
        simp only [Prosa.Classic.Model.Schedule.Uni.Susp.Schedule.ScheduleWithSuspensions.backlogged, pending,
          ARRhp, NOTCOMPhp, NOTSUSPs, scheduled_at, SS, Bool.and_true, Bool.true_and]
        simp
      obtain ⟨j_x, SCHEDx⟩ := H_work_conserving j_hp k ARRINhp BACK
      simp [scheduled_at, SS] at SCHEDx
    | some j_s =>
      simp only
      obtain ⟨ARRs, INs, PENDw, NSw⟩ := SFACTS j_s SS
      split
      · rfl
      · next NOTPEND =>
        exfalso
        apply NOTPEND
        simp only [PENDw, NSw, Bool.true_and]
        by_cases EQ : j_hp = j_s
        · subst EQ; exact H_priority_is_reflexive k j_hp
        · have NOTSCHEDhp : (!scheduled_at sched_susp j_hp k) = true := by
            simp only [scheduled_at, SS, Option.some.injEq, Bool.not_eq_true', decide_eq_false_iff_not]
            exact fun h => EQ h.symm
          have BACK : Prosa.Classic.Model.Schedule.Uni.Susp.Schedule.ScheduleWithSuspensions.backlogged job_arrival
              job_cost job_suspension_duration sched_susp j_hp k = true := by
            simp only [Prosa.Classic.Model.Schedule.Uni.Susp.Schedule.ScheduleWithSuspensions.backlogged, pending,
              ARRhp, NOTCOMPhp, NOTSUSPs, NOTSCHEDhp, Bool.and_self]
          exact H_respects_priority j_hp j_s k ARRINhp BACK (by simp [scheduled_at, SS])

theorem scheduled_in_susp_iff_scheduled_in_wcet {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time) (arr_seq : arrival_sequence Job)
    (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq)
    (higher_eq_priority : JLDP_policy Job) (H_priority_is_reflexive : JLDP_is_reflexive higher_eq_priority)
    (sched_susp : schedule Job) (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched_susp arr_seq)
    (job_suspension_duration : job_suspension Job)
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched_susp)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched_susp)
    (H_work_conserving : work_conserving job_arrival job_cost job_suspension_duration arr_seq sched_susp)
    (H_respects_priority :
      respects_JLDP_policy job_arrival job_cost job_suspension_duration arr_seq sched_susp higher_eq_priority)
    (H_respects_self_suspensions : respects_self_suspensions job_arrival job_cost job_suspension_duration sched_susp)
    (j : Job) (inflated_job_cost : Job → time) (H_cost_of_j_does_not_decrease : job_cost j ≤ inflated_job_cost j)
    (H_inflation_only_for_job_j : ∀ any_j, (!decide (any_j = j)) = true → inflated_job_cost any_j = job_cost any_j) :
    ∀ t any_j, (!completed_by job_cost sched_susp j t) = true →
      scheduled_at sched_susp any_j t = scheduled_at (sched_susp_highercost job_arrival arr_seq higher_eq_priority sched_susp job_suspension_duration inflated_job_cost) any_j t := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t IHtmp =>
    intro any_j NOTCOMP
    apply sched_susp_highercost_same_schedule job_arrival job_cost arr_seq H_arrival_times_are_consistent higher_eq_priority H_priority_is_reflexive sched_susp H_jobs_come_from_arrival_sequence job_suspension_duration H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_work_conserving H_respects_priority H_respects_self_suspensions j inflated_job_cost H_cost_of_j_does_not_decrease H_inflation_only_for_job_j t NOTCOMP _ t (Nat.le_refl t)
    intro k y LT
    apply IHtmp k LT y
    cases COMPk : completed_by job_cost sched_susp j k
    · rfl
    · have := completion_monotonic job_cost sched_susp j k t (Nat.le_of_lt LT) COMPk
      rw [this] at NOTCOMP; exact absurd NOTCOMP (by simp)

/-! ### Comparison of response-time bounds -/

theorem sched_susp_highercost_same_service_for_j {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time) (arr_seq : arrival_sequence Job)
    (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq)
    (higher_eq_priority : JLDP_policy Job) (H_priority_is_reflexive : JLDP_is_reflexive higher_eq_priority)
    (sched_susp : schedule Job) (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched_susp arr_seq)
    (job_suspension_duration : job_suspension Job)
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched_susp)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched_susp)
    (H_work_conserving : work_conserving job_arrival job_cost job_suspension_duration arr_seq sched_susp)
    (H_respects_priority :
      respects_JLDP_policy job_arrival job_cost job_suspension_duration arr_seq sched_susp higher_eq_priority)
    (H_respects_self_suspensions : respects_self_suspensions job_arrival job_cost job_suspension_duration sched_susp)
    (j : Job) (inflated_job_cost : Job → time) (H_cost_of_j_does_not_decrease : job_cost j ≤ inflated_job_cost j)
    (H_inflation_only_for_job_j : ∀ any_j, (!decide (any_j = j)) = true → inflated_job_cost any_j = job_cost any_j)
    (H_cost_j_positive : 0 < job_cost j) (r : time) (H_response_time_bound_is_tight : ∀ r', is_response_time_bound_of_job job_arrival job_cost sched_susp j r' = true → r ≤ r') :
    ∀ t : Nat, t ≤ job_arrival j + r → service sched_susp j t = service (sched_susp_highercost job_arrival arr_seq higher_eq_priority sched_susp job_suspension_duration inflated_job_cost) j t := by
  intro t
  induction t with
  | zero => intro _; simp [service, service_during]
  | succ t IHt =>
    intro LT
    have IH := IHt (by omega')
    have NOTCOMP : (!completed_by job_cost sched_susp j t) = true := by
      cases COMPt : completed_by job_cost sched_susp j t
      · rfl
      · exfalso
        by_cases AFTER : job_arrival j ≤ t
        · have B := H_response_time_bound_is_tight (t - job_arrival j)
            (by unfold is_response_time_bound_of_job; rw [show job_arrival j + (t - job_arrival j) = t by omega']
                exact COMPt)
          omega'
        · have ZERO := cumulative_service_before_job_arrival_zero job_arrival sched_susp
            H_jobs_must_arrive_to_execute j 0 t (by omega')
          simp only [completed_by, decide_eq_true_eq, service, service_during, ZERO] at COMPt
          omega'
    have SAME := scheduled_in_susp_iff_scheduled_in_wcet job_arrival job_cost arr_seq H_arrival_times_are_consistent higher_eq_priority H_priority_is_reflexive sched_susp H_jobs_come_from_arrival_sequence job_suspension_duration H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_work_conserving H_respects_priority H_respects_self_suspensions j inflated_job_cost H_cost_of_j_does_not_decrease H_inflation_only_for_job_j t j NOTCOMP
    unfold service service_during
    rw [Finset.sum_Ico_succ_top (Nat.zero_le _), Finset.sum_Ico_succ_top (Nat.zero_le _)]
    unfold service service_during at IH
    rw [IH]
    simp only [service_at, SAME]

theorem sched_susp_highercost_r_le_R {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time) (arr_seq : arrival_sequence Job)
    (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq)
    (higher_eq_priority : JLDP_policy Job) (H_priority_is_reflexive : JLDP_is_reflexive higher_eq_priority)
    (sched_susp : schedule Job) (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched_susp arr_seq)
    (job_suspension_duration : job_suspension Job)
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched_susp)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched_susp)
    (H_work_conserving : work_conserving job_arrival job_cost job_suspension_duration arr_seq sched_susp)
    (H_respects_priority :
      respects_JLDP_policy job_arrival job_cost job_suspension_duration arr_seq sched_susp higher_eq_priority)
    (H_respects_self_suspensions : respects_self_suspensions job_arrival job_cost job_suspension_duration sched_susp)
    (j : Job) (inflated_job_cost : Job → time) (H_cost_of_j_does_not_decrease : job_cost j ≤ inflated_job_cost j)
    (H_inflation_only_for_job_j : ∀ any_j, (!decide (any_j = j)) = true → inflated_job_cost any_j = job_cost any_j)
    (H_cost_j_positive : 0 < job_cost j) (r : time) (H_response_time_bound_in_sched_susp : is_response_time_bound_of_job job_arrival job_cost sched_susp j r = true)
    (H_response_time_bound_is_tight : ∀ r', is_response_time_bound_of_job job_arrival job_cost sched_susp j r' = true → r ≤ r')
    (R : time) (H_response_time_bound_in_sched_susp_highercost :
      is_response_time_bound_of_job job_arrival inflated_job_cost (sched_susp_highercost job_arrival arr_seq higher_eq_priority sched_susp job_suspension_duration inflated_job_cost) j R = true) : r ≤ R := by
  have SAME := sched_susp_highercost_same_service_for_j job_arrival job_cost arr_seq H_arrival_times_are_consistent higher_eq_priority H_priority_is_reflexive sched_susp H_jobs_come_from_arrival_sequence job_suspension_duration H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_work_conserving H_respects_priority H_respects_self_suspensions j inflated_job_cost H_cost_of_j_does_not_decrease H_inflation_only_for_job_j H_cost_j_positive r
    H_response_time_bound_is_tight
  by_contra LT
  have LT' : R < r := by omega'
  have RESPs := of_decide_eq_true H_response_time_bound_in_sched_susp
  have RESPw := of_decide_eq_true H_response_time_bound_in_sched_susp_highercost
  have EQc := H_completed_jobs_dont_execute j (job_arrival j + r)
  have SPLIT : service sched_susp j (job_arrival j + r) = service sched_susp j (job_arrival j + R) +
      service_during sched_susp j (job_arrival j + R) (job_arrival j + r) := by
    unfold service service_during
    rw [Finset.sum_Ico_consecutive _ (Nat.zero_le _) (by omega')]
  have S1 := SAME (job_arrival j + R) (by omega')
  have POS : 0 < service_during sched_susp j (job_arrival j + R) (job_arrival j + r) := by
    rcases Nat.eq_zero_or_pos (service_during sched_susp j (job_arrival j + R) (job_arrival j + r)) with Z | P
    · exfalso
      have B := H_response_time_bound_is_tight R (by
        unfold is_response_time_bound_of_job completed_by
        exact decide_eq_true (by omega'))
      omega'
    · exact P
  omega'

theorem R_bounds_inflated_cost {Job : Type v} [DecidableEq Job] (job_arrival : Job → time) (arr_seq : arrival_sequence Job)
    (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq)
    (higher_eq_priority : JLDP_policy Job) (sched_susp : schedule Job)
    (job_suspension_duration : job_suspension Job)
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched_susp) (j : Job)
    (inflated_job_cost : Job → time)
    (R : time) (H_response_time_bound_in_sched_susp_highercost :
      is_response_time_bound_of_job job_arrival inflated_job_cost (sched_susp_highercost job_arrival arr_seq higher_eq_priority sched_susp job_suspension_duration inflated_job_cost) j R = true) : inflated_job_cost j ≤ R := by
  have RESPw := of_decide_eq_true H_response_time_bound_in_sched_susp_highercost
  have MUST := sched_susp_highercost_jobs_must_arrive_to_execute job_arrival arr_seq H_arrival_times_are_consistent higher_eq_priority sched_susp job_suspension_duration H_jobs_must_arrive_to_execute inflated_job_cost
  have IGN := ignore_service_before_arrival job_arrival (sched_susp_highercost job_arrival arr_seq higher_eq_priority sched_susp job_suspension_duration inflated_job_cost) MUST j 0 (job_arrival j + R) (Nat.zero_le _)
    (Nat.le_add_right _ _)
  have DELTA := cumulative_service_le_delta (sched_susp_highercost job_arrival arr_seq higher_eq_priority sched_susp job_suspension_duration inflated_job_cost) j (job_arrival j) R
  unfold service service_during at RESPw
  unfold service_during at DELTA
  rw [IGN] at RESPw
  omega'

theorem sched_susp_highercost_incurs_more_interference {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time) (arr_seq : arrival_sequence Job)
    (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq)
    (higher_eq_priority : JLDP_policy Job) (H_priority_is_reflexive : JLDP_is_reflexive higher_eq_priority)
    (sched_susp : schedule Job) (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched_susp arr_seq)
    (job_suspension_duration : job_suspension Job)
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched_susp)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched_susp)
    (H_work_conserving : work_conserving job_arrival job_cost job_suspension_duration arr_seq sched_susp)
    (H_respects_priority :
      respects_JLDP_policy job_arrival job_cost job_suspension_duration arr_seq sched_susp higher_eq_priority)
    (H_respects_self_suspensions : respects_self_suspensions job_arrival job_cost job_suspension_duration sched_susp)
    (j : Job) (inflated_job_cost : Job → time) (H_cost_of_j_does_not_decrease : job_cost j ≤ inflated_job_cost j)
    (H_inflation_only_for_job_j : ∀ any_j, (!decide (any_j = j)) = true → inflated_job_cost any_j = job_cost any_j)
    (H_cost_j_positive : 0 < job_cost j) (r : time) (H_response_time_bound_in_sched_susp : is_response_time_bound_of_job job_arrival job_cost sched_susp j r = true)
    (H_response_time_bound_is_tight : ∀ r', is_response_time_bound_of_job job_arrival job_cost sched_susp j r' = true → r ≤ r')
    (R : time) (H_response_time_bound_in_sched_susp_highercost :
      is_response_time_bound_of_job job_arrival inflated_job_cost (sched_susp_highercost job_arrival arr_seq higher_eq_priority sched_susp job_suspension_duration inflated_job_cost) j R = true) : r - job_cost j ≤ R - inflated_job_cost j := by
  have LEQ := sched_susp_highercost_r_le_R job_arrival job_cost arr_seq H_arrival_times_are_consistent higher_eq_priority H_priority_is_reflexive sched_susp H_jobs_come_from_arrival_sequence job_suspension_duration H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_work_conserving H_respects_priority H_respects_self_suspensions j inflated_job_cost H_cost_of_j_does_not_decrease H_inflation_only_for_job_j H_cost_j_positive r H_response_time_bound_in_sched_susp
    H_response_time_bound_is_tight R H_response_time_bound_in_sched_susp_highercost
  have SAME := sched_susp_highercost_same_service_for_j job_arrival job_cost arr_seq H_arrival_times_are_consistent higher_eq_priority H_priority_is_reflexive sched_susp H_jobs_come_from_arrival_sequence job_suspension_duration H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_work_conserving H_respects_priority H_respects_self_suspensions j inflated_job_cost H_cost_of_j_does_not_decrease H_inflation_only_for_job_j H_cost_j_positive r
    H_response_time_bound_is_tight (job_arrival j + r) (Nat.le_refl _)
  have RESPs := of_decide_eq_true H_response_time_bound_in_sched_susp
  have RESPw := of_decide_eq_true H_response_time_bound_in_sched_susp_highercost
  have EQc := H_completed_jobs_dont_execute j (job_arrival j + r)
  have SPLIT : service (sched_susp_highercost job_arrival arr_seq higher_eq_priority sched_susp job_suspension_duration inflated_job_cost) j (job_arrival j + R) = service (sched_susp_highercost job_arrival arr_seq higher_eq_priority sched_susp job_suspension_duration inflated_job_cost) j (job_arrival j + r) +
      service_during (sched_susp_highercost job_arrival arr_seq higher_eq_priority sched_susp job_suspension_duration inflated_job_cost) j (job_arrival j + r) (job_arrival j + R) := by
    unfold service service_during
    rw [Finset.sum_Ico_consecutive _ (Nat.zero_le _) (by omega')]
  have DELTA := cumulative_service_le_delta (sched_susp_highercost job_arrival arr_seq higher_eq_priority sched_susp job_suspension_duration inflated_job_cost) j (job_arrival j + r) (R - r)
  rw [show job_arrival j + r + (R - r) = job_arrival j + R by omega'] at DELTA
  omega'

end Prosa.Classic.Analysis.Uni.Susp.Sustainability.Singlecost.ReductionProperties.SustainabilitySingleCostProperties
