-- Authoritative source:
-- ProsaBuddy classic Prosa (prosabuddy commit f692cb7479780cf6009493f373a309e13165201c)
-- source: classic/analysis/uni/susp/dynamic/oblivious/reduction.v
-- sha256: see Prosa-Shunqi/classic-prosa/comprehensive-classic/file_order.csv (rank 131)

import Prosa.Classic.Util.All
import Prosa.Classic.Model.Arrival.Basic.Job
import Prosa.Classic.Model.Arrival.Basic.Task
import Prosa.Classic.Model.Arrival.Basic.ArrivalSequence
import Prosa.Classic.Model.Priority
import Prosa.Classic.Model.Suspension
import Prosa.Classic.Model.Schedule.Uni.Schedule
import Prosa.Classic.Model.Schedule.Uni.Schedulability
import Prosa.Classic.Model.Schedule.Uni.Basic.Platform
import Prosa.Classic.Model.Schedule.Uni.Susp.SuspensionIntervals
import Prosa.Classic.Model.Schedule.Uni.Susp.Schedule
import Prosa.Classic.Model.Schedule.Uni.Susp.Platform
import Prosa.Classic.Model.Schedule.Uni.Transformation.Construction
import Prosa.Classic.Implementation.Uni.Basic.Schedule

/-!
Reduction from a suspension-aware schedule to a suspension-oblivious schedule with inflated job costs (Rocq
module `ReductionToBasicSchedule` of `classic/analysis/uni/susp/dynamic/oblivious/reduction.v`).

Representation notes:
* The Rocq module aliases `susp := ScheduleWithSuspensions`, `susp_oblivious := Platform` and
  `susp_aware := PlatformWithSuspensions` are Lean namespace abbreviations of the accepted classic modules.
* `[seq j <- s | P j]` is `s.filter P`; `if o is Some x then a else b` is a `match`; `~~ b` is `(!b) = true`;
  a `bool` used as a `nat` (e.g. `scheduled_at sched j t <= …`) is `Bool.toNat`.
* The section-local `Let`s (`job_total_suspension`, `jobs_are_valid`, `tasks_are_valid`, `job_is_pending`,
  `empty_schedule`, `job_suspended_at`, `job_cumulative_suspension`, `job_service_with_suspensions`,
  `job_service_without_suspensions`, `schedulable_without_suspensions`, `schedulable_with_suspensions`) are
  unfolded.
* Binder lists follow the Rocq contract (section hypotheses appear only where the Rocq proof uses them).
-/

set_option linter.dupNamespace false
set_option linter.unusedVariables false

namespace Prosa.Classic.Analysis.Uni.Susp.Dynamic.Oblivious.Reduction.ReductionToBasicSchedule

open Prosa.Classic.Model.Time.Time
open Prosa.Classic.Model.Arrival.Basic.ArrivalSequence.ArrivalSequence
open Prosa.Classic.Model.Arrival.Basic.Job.Job
open Prosa.Classic.Model.Arrival.Basic.Task.SporadicTaskset
open Prosa.Classic.Model.Priority.Priority
open Prosa.Classic.Model.Suspension.Suspension
open Prosa.Classic.Model.Schedule.Uni.Schedule.UniprocessorSchedule
open Prosa.Classic.Model.Schedule.Uni.Schedulability.Schedulability (job_misses_no_deadline)
open Prosa.Classic.Model.Schedule.Uni.Susp.SuspensionIntervals.SuspensionIntervals
open Prosa.Classic.Model.Schedule.Uni.Transformation.Construction.ScheduleConstruction
open Prosa.Classic.Util.Minmax (seq_min seq_min_in_seq seq_min_exists seq_min_computes_min)

namespace susp
export Prosa.Classic.Model.Schedule.Uni.Susp.Schedule.ScheduleWithSuspensions (backlogged)
end susp
namespace susp_oblivious
export Prosa.Classic.Model.Schedule.Uni.Basic.Platform.Platform (work_conserving respects_JLDP_policy)
end susp_oblivious
namespace susp_aware
export Prosa.Classic.Model.Schedule.Uni.Susp.Platform.PlatformWithSuspensions (work_conserving respects_JLDP_policy)
end susp_aware

universe u v

local macro "omega'" : tactic =>
  `(tactic| ((try dsimp only [Prosa.Classic.Model.Time.Time.time,
    Prosa.Classic.Model.Time.Time.instant, Prosa.Classic.Model.Time.Time.duration] at *) <;>
    omega))

/-! ### Cost inflation -/

def inflated_job_cost {Job : Type v} [DecidableEq Job] (original_job_cost : Job → time) (next_suspension : job_suspension Job) (j : Job) : Nat :=
  original_job_cost j + total_suspension original_job_cost next_suspension j

def inflated_task_cost {Task : Type u} [DecidableEq Task] (original_task_cost task_suspension_bound : Task → time)
    (tsk : Task) : Nat :=
  original_task_cost tsk + task_suspension_bound tsk

theorem suspension_oblivious_job_parameters_remain_valid {Task : Type u} [DecidableEq Task]
    (task_period task_deadline : Task → time) {Job : Type v} [DecidableEq Job] (job_deadline : Job → time) (job_task : Job → Task)
    (ts : List Task) (arr_seq : arrival_sequence Job) (H_jobs_from_taskset : ∀ j, arrives_in arr_seq j → job_task j ∈ ts)
    (original_job_cost : Job → time) (original_task_cost : Task → time) (next_suspension : job_suspension Job)
    (task_suspension_bound : Task → time)
    (H_dynamic_suspensions :
      dynamic_suspension_model original_job_cost job_task next_suspension task_suspension_bound)
    (H_inflated_cost_le_deadline_and_period : ∀ tsk, tsk ∈ ts →
      inflated_task_cost original_task_cost task_suspension_bound tsk ≤ task_deadline tsk ∧
        inflated_task_cost original_task_cost task_suspension_bound tsk ≤ task_period tsk) :
    (∀ j, arrives_in arr_seq j →
      valid_sporadic_job original_task_cost task_deadline original_job_cost job_deadline job_task j) →
    ∀ j, arrives_in arr_seq j →
      valid_sporadic_job (inflated_task_cost original_task_cost task_suspension_bound) task_deadline
        (inflated_job_cost original_job_cost next_suspension) job_deadline job_task j := by
  intro VALIDjob j ARRj
  obtain ⟨⟨POS, LEDL, DLPOS⟩, LETC, DLEQ⟩ := VALIDjob j ARRj
  have LEdl := (H_inflated_cost_le_deadline_and_period (job_task j) (H_jobs_from_taskset j ARRj)).1
  have DYN := H_dynamic_suspensions j
  have POS' : 0 < original_job_cost j := of_decide_eq_true POS
  have LETC' : original_job_cost j ≤ original_task_cost (job_task j) := of_decide_eq_true LETC
  unfold job_deadline_eq_task_deadline at DLEQ
  have LEC : inflated_job_cost original_job_cost next_suspension j ≤
      inflated_task_cost original_task_cost task_suspension_bound (job_task j) := by
    unfold inflated_job_cost inflated_task_cost; omega'
  refine ⟨⟨decide_eq_true ?_, decide_eq_true ?_, DLPOS⟩, decide_eq_true LEC, DLEQ⟩
  · unfold inflated_job_cost; omega'
  · rw [DLEQ]; exact Nat.le_trans LEC LEdl

theorem suspension_oblivious_task_parameters_remain_valid {Task : Type u} [DecidableEq Task]
    (task_period task_deadline : Task → time) (ts : List Task) (original_task_cost task_suspension_bound : Task → time)
    (H_inflated_cost_le_deadline_and_period : ∀ tsk, tsk ∈ ts →
      inflated_task_cost original_task_cost task_suspension_bound tsk ≤ task_deadline tsk ∧
        inflated_task_cost original_task_cost task_suspension_bound tsk ≤ task_period tsk) :
    valid_sporadic_taskset original_task_cost task_period task_deadline ts →
      valid_sporadic_taskset (inflated_task_cost original_task_cost task_suspension_bound) task_period
        task_deadline ts := by
  intro VALIDtask tsk IN
  obtain ⟨CPOS, PPOS, DPOS, _, _⟩ := VALIDtask tsk IN
  obtain ⟨LEdl, LEp⟩ := H_inflated_cost_le_deadline_and_period tsk IN
  have CPOS' : 0 < original_task_cost tsk := of_decide_eq_true CPOS
  refine ⟨decide_eq_true ?_, PPOS, DPOS, ?_, ?_⟩
  · unfold inflated_task_cost; omega'
  · exact decide_eq_true LEdl
  · exact decide_eq_true LEp

/-! ### Schedule construction -/

def pending_jobs {Job : Type v} [DecidableEq Job] (job_arrival : Job → time) (arr_seq : arrival_sequence Job) (original_job_cost : Job → time) (next_suspension : job_suspension Job)
    (sched_prefix : schedule Job) (t : time) : List Job :=
  (jobs_arrived_up_to arr_seq t).filter (fun j => pending job_arrival (inflated_job_cost original_job_cost next_suspension) sched_prefix j t)

def highest_priority_job {Job : Type v} [DecidableEq Job] (job_arrival : Job → time) (arr_seq : arrival_sequence Job) (higher_eq_priority : JLDP_policy Job) (original_job_cost : Job → time)
    (next_suspension : job_suspension Job) (sched_prefix : schedule Job) (t : time) : Option Job :=
  seq_min (higher_eq_priority t) (pending_jobs job_arrival arr_seq original_job_cost next_suspension sched_prefix t)

def build_schedule {Job : Type v} [DecidableEq Job] (job_arrival : Job → time) (arr_seq : arrival_sequence Job) (higher_eq_priority : JLDP_policy Job) (original_job_cost : Job → time) (next_suspension : job_suspension Job) (sched_susp : schedule Job) (sched_prefix : schedule Job) (t : time) : Option Job :=
  match highest_priority_job job_arrival arr_seq higher_eq_priority original_job_cost next_suspension sched_prefix t with
  | some j_hp =>
    match sched_susp t with
    | some j_sched =>
      if (pending job_arrival (inflated_job_cost original_job_cost next_suspension) sched_prefix j_sched t && higher_eq_priority t j_sched j_hp) then some j_sched
      else highest_priority_job job_arrival arr_seq higher_eq_priority original_job_cost next_suspension sched_prefix t
    | none => highest_priority_job job_arrival arr_seq higher_eq_priority original_job_cost next_suspension sched_prefix t
  | none => highest_priority_job job_arrival arr_seq higher_eq_priority original_job_cost next_suspension sched_prefix t

def sched_new {Job : Type v} [DecidableEq Job] (job_arrival : Job → time) (arr_seq : arrival_sequence Job) (higher_eq_priority : JLDP_policy Job) (original_job_cost : Job → time) (next_suspension : job_suspension Job) (sched_susp : schedule Job) : schedule Job :=
  build_schedule_from_prefixes (build_schedule job_arrival arr_seq higher_eq_priority original_job_cost next_suspension sched_susp) (fun _ => none)

theorem sched_new_depends_only_on_service {Job : Type v} [DecidableEq Job] (job_arrival : Job → time) (arr_seq : arrival_sequence Job) (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq) (higher_eq_priority : JLDP_policy Job) (original_job_cost : Job → time) (next_suspension : job_suspension Job) (sched_susp : schedule Job) :
    ∀ (sched1 sched2 : schedule Job) (t : time), (∀ j, service sched1 j t = service sched2 j t) →
      build_schedule job_arrival arr_seq higher_eq_priority original_job_cost next_suspension sched_susp sched1 t = build_schedule job_arrival arr_seq higher_eq_priority original_job_cost next_suspension sched_susp sched2 t := by
  intro sched1 sched2 t ALL
  have SAME : ∀ j, pending job_arrival (inflated_job_cost original_job_cost next_suspension) sched1 j t = pending job_arrival (inflated_job_cost original_job_cost next_suspension) sched2 j t := by
    intro j; simp only [pending, completed_by, ALL]
  unfold build_schedule highest_priority_job pending_jobs
  simp only [SAME]

theorem sched_new_uses_construction_function {Job : Type v} [DecidableEq Job] (job_arrival : Job → time) (arr_seq : arrival_sequence Job) (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq) (higher_eq_priority : JLDP_policy Job) (original_job_cost : Job → time) (next_suspension : job_suspension Job) (sched_susp : schedule Job) :
    ∀ t, (sched_new job_arrival arr_seq higher_eq_priority original_job_cost next_suspension sched_susp) t = build_schedule job_arrival arr_seq higher_eq_priority original_job_cost next_suspension sched_susp (sched_new job_arrival arr_seq higher_eq_priority original_job_cost next_suspension sched_susp) t := by
  intro t
  exact service_dependent_schedule_construction _ _
    (sched_new_depends_only_on_service job_arrival arr_seq H_arrival_times_are_consistent higher_eq_priority original_job_cost next_suspension sched_susp) t

/-- LEAN_HELPER: the job picked by `highest_priority_job` is a pending job. -/
private theorem hp_in_pending_jobs {Job : Type v} [DecidableEq Job] (job_arrival : Job → time) (arr_seq : arrival_sequence Job) (higher_eq_priority : JLDP_policy Job) (original_job_cost : Job → time)
    (next_suspension : job_suspension Job) (sched : schedule Job) (t : time) (j : Job)
    (HP : highest_priority_job job_arrival arr_seq higher_eq_priority original_job_cost next_suspension sched t = some j) : j ∈ pending_jobs job_arrival arr_seq original_job_cost next_suspension sched t :=
  seq_min_in_seq _ _ _ HP

/-- LEAN_HELPER: a job picked by the construction function is pending, and is either a pending job of the
generated prefix or the job scheduled in the original schedule. -/
private theorem build_schedule_some {Job : Type v} [DecidableEq Job] (job_arrival : Job → time) (arr_seq : arrival_sequence Job) (higher_eq_priority : JLDP_policy Job) (original_job_cost : Job → time) (next_suspension : job_suspension Job) (sched_susp : schedule Job) (sched : schedule Job) (t : time) (j : Job)
    (SOME : build_schedule job_arrival arr_seq higher_eq_priority original_job_cost next_suspension sched_susp sched t = some j) :
    pending job_arrival (inflated_job_cost original_job_cost next_suspension) sched j t = true ∧ (j ∈ pending_jobs job_arrival arr_seq original_job_cost next_suspension sched t ∨ sched_susp t = some j) := by
  have INP : ∀ x, x ∈ pending_jobs job_arrival arr_seq original_job_cost next_suspension sched t → pending job_arrival (inflated_job_cost original_job_cost next_suspension) sched x t = true := by
    intro x IN; unfold pending_jobs at IN; exact (List.mem_filter.mp IN).2
  unfold build_schedule at SOME
  cases HP : highest_priority_job job_arrival arr_seq higher_eq_priority original_job_cost next_suspension sched t with
  | none => rw [HP] at SOME; simp at SOME
  | some j_hp =>
    rw [HP] at SOME
    simp only at SOME
    cases SUSP : sched_susp t with
    | none =>
      rw [SUSP] at SOME; simp only [HP] at SOME
      have := hp_in_pending_jobs job_arrival arr_seq higher_eq_priority original_job_cost next_suspension sched t j
        (by rw [HP]; simpa using SOME)
      exact ⟨INP j this, Or.inl this⟩
    | some j_sched =>
      rw [SUSP] at SOME; simp only at SOME
      split at SOME
      · next COND =>
        cases SOME
        simp only [Bool.and_eq_true] at COND
        exact ⟨COND.1, Or.inr rfl⟩
      · have := hp_in_pending_jobs job_arrival arr_seq higher_eq_priority original_job_cost next_suspension sched t j
          (by rw [HP]; simpa using SOME)
        exact ⟨INP j this, Or.inl this⟩

/-- LEAN_HELPER: a job scheduled in the generated schedule is pending there. -/
private theorem sched_new_scheduled_pending {Job : Type v} [DecidableEq Job] (job_arrival : Job → time) (arr_seq : arrival_sequence Job) (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq) (higher_eq_priority : JLDP_policy Job) (original_job_cost : Job → time) (next_suspension : job_suspension Job) (sched_susp : schedule Job) (j : Job) (t : time)
    (SCHED : scheduled_at (sched_new job_arrival arr_seq higher_eq_priority original_job_cost next_suspension sched_susp) j t = true) :
    pending job_arrival (inflated_job_cost original_job_cost next_suspension) (sched_new job_arrival arr_seq higher_eq_priority original_job_cost next_suspension sched_susp) j t = true ∧ (j ∈ pending_jobs job_arrival arr_seq original_job_cost next_suspension (sched_new job_arrival arr_seq higher_eq_priority original_job_cost next_suspension sched_susp) t ∨ sched_susp t = some j) := by
  simp only [scheduled_at, decide_eq_true_eq] at SCHED
  rw [sched_new_uses_construction_function job_arrival arr_seq H_arrival_times_are_consistent higher_eq_priority original_job_cost next_suspension sched_susp] at SCHED
  exact build_schedule_some job_arrival arr_seq higher_eq_priority original_job_cost next_suspension sched_susp _ t j
    SCHED

theorem sched_newjobs_come_from_arrival_sequence {Job : Type v} [DecidableEq Job] (job_arrival : Job → time) (arr_seq : arrival_sequence Job) (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq) (higher_eq_priority : JLDP_policy Job) (original_job_cost : Job → time) (next_suspension : job_suspension Job) (sched_susp : schedule Job) (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched_susp arr_seq) :
    jobs_come_from_arrival_sequence (sched_new job_arrival arr_seq higher_eq_priority original_job_cost next_suspension sched_susp) arr_seq := by
  intro j t SCHED
  rcases (sched_new_scheduled_pending job_arrival arr_seq H_arrival_times_are_consistent higher_eq_priority original_job_cost next_suspension sched_susp j t SCHED).2 with IN | SUSP
  · unfold pending_jobs at IN
    exact in_arrivals_implies_arrived arr_seq j 0 (t + 1) (List.mem_filter.mp IN).1
  · exact H_jobs_come_from_arrival_sequence j t (by simp [scheduled_at, SUSP])

theorem sched_new_jobs_must_arrive_to_execute {Job : Type v} [DecidableEq Job] (job_arrival : Job → time) (arr_seq : arrival_sequence Job) (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq) (higher_eq_priority : JLDP_policy Job) (original_job_cost : Job → time) (next_suspension : job_suspension Job) (sched_susp : schedule Job) :
    jobs_must_arrive_to_execute job_arrival (sched_new job_arrival arr_seq higher_eq_priority original_job_cost next_suspension sched_susp) := by
  intro j t SCHED
  have PEND := (sched_new_scheduled_pending job_arrival arr_seq H_arrival_times_are_consistent higher_eq_priority original_job_cost next_suspension sched_susp j t SCHED).1
  simp only [pending, Bool.and_eq_true] at PEND
  exact PEND.1

theorem sched_new_completed_jobs_dont_execute {Job : Type v} [DecidableEq Job] (job_arrival : Job → time) (arr_seq : arrival_sequence Job) (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq) (higher_eq_priority : JLDP_policy Job) (original_job_cost : Job → time) (next_suspension : job_suspension Job) (sched_susp : schedule Job) :
    completed_jobs_dont_execute (inflated_job_cost original_job_cost next_suspension) (sched_new job_arrival arr_seq higher_eq_priority original_job_cost next_suspension sched_susp) := by
  intro j t
  induction t with
  | zero => simp [service, service_during]
  | succ t IHt =>
    have STEP : service (sched_new job_arrival arr_seq higher_eq_priority original_job_cost next_suspension sched_susp) j (t + 1) = service (sched_new job_arrival arr_seq higher_eq_priority original_job_cost next_suspension sched_susp) j t + service_at (sched_new job_arrival arr_seq higher_eq_priority original_job_cost next_suspension sched_susp) j t := by
      unfold service service_during
      rw [Finset.sum_Ico_succ_top (Nat.zero_le _)]
    rw [STEP]
    rcases Nat.lt_or_ge (service (sched_new job_arrival arr_seq higher_eq_priority original_job_cost next_suspension sched_susp) j t) ((inflated_job_cost original_job_cost next_suspension) j) with LT | GE
    · have : service_at (sched_new job_arrival arr_seq higher_eq_priority original_job_cost next_suspension sched_susp) j t ≤ 1 := by
        unfold service_at; cases scheduled_at _ j t <;> simp
      omega'
    · have NS : scheduled_at (sched_new job_arrival arr_seq higher_eq_priority original_job_cost next_suspension sched_susp) j t = false := by
        cases hs : scheduled_at (sched_new job_arrival arr_seq higher_eq_priority original_job_cost next_suspension sched_susp) j t
        · rfl
        · have PEND := (sched_new_scheduled_pending job_arrival arr_seq H_arrival_times_are_consistent higher_eq_priority original_job_cost next_suspension sched_susp j t hs).1
          simp only [pending, completed_by, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at PEND
          exact absurd GE PEND.2
      simp only [service_at, NS, Bool.toNat_false, Nat.add_zero]
      exact IHt

/-- LEAN_HELPER: a backlogged job of the arrival sequence is a pending job of the generated prefix. -/
private theorem backlogged_in_pending_jobs {Job : Type v} [DecidableEq Job] (job_arrival : Job → time) (arr_seq : arrival_sequence Job) (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq) (original_job_cost : Job → time)
    (next_suspension : job_suspension Job) (sched : schedule Job) (j : Job) (t : time) (IN : arrives_in arr_seq j)
    (PEND : pending job_arrival (inflated_job_cost original_job_cost next_suspension) sched j t = true) : j ∈ pending_jobs job_arrival arr_seq original_job_cost next_suspension sched t := by
  unfold pending_jobs
  rw [List.mem_filter]
  refine ⟨?_, PEND⟩
  have ARR := PEND
  simp only [pending, has_arrived, Bool.and_eq_true, decide_eq_true_eq] at ARR
  exact arrived_between_implies_in_arrivals job_arrival arr_seq H_arrival_times_are_consistent j 0 (t + 1) IN
    (by simp only [arrived_between, Bool.and_eq_true, decide_eq_true_eq]; omega')

theorem sched_new_work_conserving {Job : Type v} [DecidableEq Job] (job_arrival : Job → time) (arr_seq : arrival_sequence Job) (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq) (higher_eq_priority : JLDP_policy Job) (original_job_cost : Job → time) (next_suspension : job_suspension Job) (sched_susp : schedule Job) :
    susp_oblivious.work_conserving job_arrival (inflated_job_cost original_job_cost next_suspension) arr_seq (sched_new job_arrival arr_seq higher_eq_priority original_job_cost next_suspension sched_susp) := by
  intro j t ARRj BACK
  simp only [backlogged, Bool.and_eq_true] at BACK
  have IN := backlogged_in_pending_jobs job_arrival arr_seq H_arrival_times_are_consistent original_job_cost
    next_suspension _ j t ARRj BACK.1
  have EX := seq_min_exists (higher_eq_priority t) _ j IN
  simp only [scheduled_at, decide_eq_true_eq]
  rw [sched_new_uses_construction_function job_arrival arr_seq H_arrival_times_are_consistent higher_eq_priority original_job_cost next_suspension sched_susp]
  unfold build_schedule
  cases HP : highest_priority_job job_arrival arr_seq higher_eq_priority original_job_cost next_suspension (sched_new job_arrival arr_seq higher_eq_priority original_job_cost next_suspension sched_susp) t with
  | none =>
    unfold highest_priority_job at HP
    rw [HP] at EX; simp at EX
  | some j_hp =>
    simp only
    cases sched_susp t with
    | none => exact ⟨j_hp, rfl⟩
    | some j0 =>
      simp only
      split
      · exact ⟨j0, rfl⟩
      · exact ⟨j_hp, rfl⟩

theorem sched_new_respects_policy {Job : Type v} [DecidableEq Job] (job_arrival : Job → time) (arr_seq : arrival_sequence Job) (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq) (higher_eq_priority : JLDP_policy Job) (H_priority_is_transitive : JLDP_is_transitive higher_eq_priority)
    (H_priority_is_total : JLDP_is_total arr_seq higher_eq_priority) (original_job_cost : Job → time) (next_suspension : job_suspension Job) (sched_susp : schedule Job) :
    susp_oblivious.respects_JLDP_policy job_arrival (inflated_job_cost original_job_cost next_suspension) arr_seq (sched_new job_arrival arr_seq higher_eq_priority original_job_cost next_suspension sched_susp) higher_eq_priority := by
  intro j j_hp t ARRj BACK SCHED
  simp only [backlogged, Bool.and_eq_true] at BACK
  have IN := backlogged_in_pending_jobs job_arrival arr_seq H_arrival_times_are_consistent original_job_cost
    next_suspension _ j t ARRj BACK.1
  simp only [scheduled_at, decide_eq_true_eq] at SCHED
  rw [sched_new_uses_construction_function job_arrival arr_seq H_arrival_times_are_consistent higher_eq_priority original_job_cost next_suspension sched_susp] at SCHED
  unfold build_schedule at SCHED
  cases HP : highest_priority_job job_arrival arr_seq higher_eq_priority original_job_cost next_suspension (sched_new job_arrival arr_seq higher_eq_priority original_job_cost next_suspension sched_susp) t with
  | none => rw [HP] at SCHED; simp at SCHED
  | some j_min =>
    have ALL : ∀ x, x ∈ pending_jobs job_arrival arr_seq original_job_cost next_suspension (sched_new job_arrival arr_seq higher_eq_priority original_job_cost next_suspension sched_susp) t → higher_eq_priority t j_min x = true := by
      intro x INx
      apply seq_min_computes_min (higher_eq_priority t) (H_priority_is_transitive t) _ _ j_min x HP INx
      intro a b INa INb
      unfold pending_jobs at INa INb
      exact H_priority_is_total a b t (in_arrivals_implies_arrived arr_seq a 0 (t + 1) (List.mem_filter.mp INa).1)
        (in_arrivals_implies_arrived arr_seq b 0 (t + 1) (List.mem_filter.mp INb).1)
    rw [HP] at SCHED
    simp only at SCHED
    cases SUSP : sched_susp t with
    | none =>
      rw [SUSP] at SCHED; simp only at SCHED
      rw [← Option.some.inj SCHED]; exact ALL j IN
    | some j0 =>
      rw [SUSP] at SCHED; simp only at SCHED
      split at SCHED
      · next COND =>
        rw [← Option.some.inj SCHED]
        simp only [Bool.and_eq_true] at COND
        exact H_priority_is_transitive t j_min j0 j COND.2 (ALL j IN)
      · rw [← Option.some.inj SCHED]; exact ALL j IN

theorem sched_new_breaks_ties {Job : Type v} [DecidableEq Job] (job_arrival : Job → time) (arr_seq : arrival_sequence Job) (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq) (higher_eq_priority : JLDP_policy Job) (original_job_cost : Job → time) (next_suspension : job_suspension Job) (sched_susp : schedule Job) :
    ∀ (j1 j2 : Job) (t : time),
      higher_eq_priority t j1 j2 = true →
      higher_eq_priority t j2 j1 = true →
      scheduled_at sched_susp j1 t = true →
      pending job_arrival (inflated_job_cost original_job_cost next_suspension) (sched_new job_arrival arr_seq higher_eq_priority original_job_cost next_suspension sched_susp) j1 t = true →
      scheduled_at (sched_new job_arrival arr_seq higher_eq_priority original_job_cost next_suspension sched_susp) j2 t = true →
      j1 = j2 := by
  intro j1 j2 t HP1 HP2 SCHEDs PEND SCHEDn
  simp only [scheduled_at, decide_eq_true_eq] at SCHEDs SCHEDn
  rw [sched_new_uses_construction_function job_arrival arr_seq H_arrival_times_are_consistent higher_eq_priority original_job_cost next_suspension sched_susp] at SCHEDn
  unfold build_schedule at SCHEDn
  cases HP : highest_priority_job job_arrival arr_seq higher_eq_priority original_job_cost next_suspension (sched_new job_arrival arr_seq higher_eq_priority original_job_cost next_suspension sched_susp) t with
  | none => rw [HP] at SCHEDn; simp at SCHEDn
  | some j_hp =>
    rw [HP] at SCHEDn
    simp only [SCHEDs, PEND, Bool.true_and] at SCHEDn
    split at SCHEDn
    · exact Option.some.inj SCHEDn
    · next NOT =>
      rw [← Option.some.inj SCHEDn] at HP1
      exact absurd HP1 (by simpa using NOT)

/-! ### Service preservation -/

theorem reduction_inductive_step_not_arrived {Job : Type v} [DecidableEq Job] (job_arrival : Job → time) (arr_seq : arrival_sequence Job) (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq) (higher_eq_priority : JLDP_policy Job) (original_job_cost : Job → time) (next_suspension : job_suspension Job) (sched_susp : schedule Job) (t : time) (j : Job) :
    (!has_arrived job_arrival j t) = true →
    service (sched_new job_arrival arr_seq higher_eq_priority original_job_cost next_suspension sched_susp) j (t + 1) ≤ service sched_susp j (t + 1) + cumulative_suspension job_arrival original_job_cost next_suspension sched_susp j (t + 1) := by
  intro NOTARR
  simp only [has_arrived, Bool.not_eq_true', decide_eq_false_iff_not] at NOTARR
  have ZERO := cumulative_service_before_job_arrival_zero job_arrival (sched_new job_arrival arr_seq higher_eq_priority original_job_cost next_suspension sched_susp)
    (sched_new_jobs_must_arrive_to_execute job_arrival arr_seq H_arrival_times_are_consistent higher_eq_priority original_job_cost next_suspension sched_susp) j 0 (t + 1) (by omega')
  have : service (sched_new job_arrival arr_seq higher_eq_priority original_job_cost next_suspension sched_susp) j (t + 1) = 0 := by unfold service service_during; exact ZERO
  rw [this]; exact Nat.zero_le _

theorem reduction_inductive_step_case1_completed {Job : Type v} [DecidableEq Job] (job_arrival : Job → time) (arr_seq : arrival_sequence Job) (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq) (higher_eq_priority : JLDP_policy Job) (original_job_cost : Job → time) (next_suspension : job_suspension Job) (sched_susp : schedule Job) (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched_susp)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute original_job_cost sched_susp)
    (H_respects_self_suspensions : respects_self_suspensions job_arrival original_job_cost next_suspension sched_susp) (t : time) (j : Job)
    (H_j_has_completed : completed_by original_job_cost sched_susp j t = true) :
    service (sched_new job_arrival arr_seq higher_eq_priority original_job_cost next_suspension sched_susp) j (t + 1) ≤ service sched_susp j (t + 1) + cumulative_suspension job_arrival original_job_cost next_suspension sched_susp j (t + 1) := by
  have LE := sched_new_completed_jobs_dont_execute job_arrival arr_seq H_arrival_times_are_consistent higher_eq_priority original_job_cost next_suspension sched_susp j (t + 1)
  have COMP' := completion_monotonic original_job_cost sched_susp j t (t + 1) (Nat.le_succ t) H_j_has_completed
  have EQ := cumulative_suspension_eq_total_suspension job_arrival original_job_cost next_suspension sched_susp
    H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_respects_self_suspensions j (t + 1) COMP'
  simp only [completed_by, decide_eq_true_eq] at COMP'
  unfold inflated_job_cost at LE
  rw [EQ]; omega'

theorem reduction_inductive_step_not_scheduled_in_new {Job : Type v} [DecidableEq Job] (job_arrival : Job → time) (arr_seq : arrival_sequence Job) (higher_eq_priority : JLDP_policy Job) (original_job_cost : Job → time) (next_suspension : job_suspension Job) (sched_susp : schedule Job) (t : time) (j : Job) :
    (!scheduled_at (sched_new job_arrival arr_seq higher_eq_priority original_job_cost next_suspension sched_susp) j t) = true →
    (scheduled_at (sched_new job_arrival arr_seq higher_eq_priority original_job_cost next_suspension sched_susp) j t).toNat ≤ (suspended_at job_arrival original_job_cost next_suspension sched_susp j t).toNat + (scheduled_at sched_susp j t).toNat := by
  intro NOT
  simp only [Bool.not_eq_true'] at NOT
  rw [NOT]; simp

theorem reduction_inductive_step_scheduled_in_susp {Job : Type v} [DecidableEq Job] (job_arrival : Job → time) (arr_seq : arrival_sequence Job) (higher_eq_priority : JLDP_policy Job) (original_job_cost : Job → time) (next_suspension : job_suspension Job) (sched_susp : schedule Job) (t : time) (j : Job) :
    scheduled_at sched_susp j t = true →
    (scheduled_at (sched_new job_arrival arr_seq higher_eq_priority original_job_cost next_suspension sched_susp) j t).toNat ≤ (suspended_at job_arrival original_job_cost next_suspension sched_susp j t).toNat + (scheduled_at sched_susp j t).toNat := by
  intro SCHED
  rw [SCHED]
  cases scheduled_at (sched_new job_arrival arr_seq higher_eq_priority original_job_cost next_suspension sched_susp) j t <;> simp

theorem reduction_inductive_step_j_is_backlogged {Job : Type v} [DecidableEq Job] (job_arrival original_job_cost : Job → time)
    (next_suspension : job_suspension Job) (sched_susp : schedule Job) (t : time) (j : Job)
    (H_j_has_arrived : has_arrived job_arrival j t = true)
    (H_j_is_pending : (!completed_by original_job_cost sched_susp j t) = true)
    (H_j_not_scheduled_in_susp : (!scheduled_at sched_susp j t) = true)
    (H_j_is_not_suspended : (!suspended_at job_arrival original_job_cost next_suspension sched_susp j t) = true) :
    susp.backlogged job_arrival original_job_cost next_suspension sched_susp j t = true := by
  simp only [susp.backlogged, pending, H_j_has_arrived, H_j_is_pending, H_j_not_scheduled_in_susp,
    H_j_is_not_suspended, Bool.and_self]

theorem reduction_inductive_step_exists_hep_job {Job : Type v} [DecidableEq Job] (job_arrival : Job → time) (arr_seq : arrival_sequence Job) (higher_eq_priority : JLDP_policy Job) (original_job_cost : Job → time) (next_suspension : job_suspension Job) (sched_susp : schedule Job) (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched_susp arr_seq)
    (H_work_conserving : susp_aware.work_conserving job_arrival original_job_cost next_suspension arr_seq sched_susp)
    (H_respects_priority : susp_aware.respects_JLDP_policy job_arrival original_job_cost next_suspension arr_seq
      sched_susp higher_eq_priority)
    (t : time) (j : Job) (H_comes_from_arrival_sequence : arrives_in arr_seq j)
    (H_j_has_arrived : has_arrived job_arrival j t = true)
    (H_j_is_pending : (!completed_by original_job_cost sched_susp j t) = true)
    (H_j_not_scheduled_in_susp : (!scheduled_at sched_susp j t) = true)
    (H_j_is_not_suspended : (!suspended_at job_arrival original_job_cost next_suspension sched_susp j t) = true) :
    ∃ j_hp, arrives_in arr_seq j_hp ∧ scheduled_at sched_susp j_hp t = true ∧ higher_eq_priority t j_hp j = true := by
  have BACKs := reduction_inductive_step_j_is_backlogged job_arrival original_job_cost next_suspension sched_susp t j
    H_j_has_arrived H_j_is_pending H_j_not_scheduled_in_susp H_j_is_not_suspended
  obtain ⟨j_hp, SCHEDhp⟩ := H_work_conserving j t H_comes_from_arrival_sequence BACKs
  exact ⟨j_hp, H_jobs_come_from_arrival_sequence j_hp t SCHEDhp, SCHEDhp,
    H_respects_priority j j_hp t H_comes_from_arrival_sequence BACKs SCHEDhp⟩

theorem reduction_inductive_step_j_hp_completed_in_new {Job : Type v} [DecidableEq Job] (job_arrival : Job → time) (arr_seq : arrival_sequence Job) (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq) (higher_eq_priority : JLDP_policy Job) (H_priority_is_transitive : JLDP_is_transitive higher_eq_priority)
    (H_priority_is_total : JLDP_is_total arr_seq higher_eq_priority) (original_job_cost : Job → time) (next_suspension : job_suspension Job) (sched_susp : schedule Job)
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched_susp)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute original_job_cost sched_susp) (t : time) (j : Job)
    (H_comes_from_arrival_sequence : arrives_in arr_seq j)
    (H_j_has_arrived : has_arrived job_arrival j t = true)
    (H_j_is_pending : (!completed_by original_job_cost sched_susp j t) = true)
    (H_j_scheduled_in_new : scheduled_at (sched_new job_arrival arr_seq higher_eq_priority original_job_cost next_suspension sched_susp) j t = true)
    (H_j_not_scheduled_in_susp : (!scheduled_at sched_susp j t) = true)
    (H_j_is_not_suspended : (!suspended_at job_arrival original_job_cost next_suspension sched_susp j t) = true)
    (j_hp : Job) (H_j_hp_comes_from_sequence : arrives_in arr_seq j_hp)
    (H_j_hp_is_scheduled : scheduled_at sched_susp j_hp t = true)
    (H_higher_or_equal_priority : higher_eq_priority t j_hp j = true) :
    completed_by (inflated_job_cost original_job_cost next_suspension) (sched_new job_arrival arr_seq higher_eq_priority original_job_cost next_suspension sched_susp) j_hp t = true := by
  have PENDhp := scheduled_implies_pending job_arrival original_job_cost sched_susp H_jobs_must_arrive_to_execute
    H_completed_jobs_dont_execute j_hp t H_j_hp_is_scheduled
  simp only [pending, Bool.and_eq_true] at PENDhp
  by_contra NOTCOMPhp
  have PENDhp' : pending job_arrival (inflated_job_cost original_job_cost next_suspension) (sched_new job_arrival arr_seq higher_eq_priority original_job_cost next_suspension sched_susp) j_hp t = true := by
    simp only [pending, PENDhp.1, Bool.true_and, Bool.not_eq_true']
    simpa using NOTCOMPhp
  cases SCHEDhp' : scheduled_at (sched_new job_arrival arr_seq higher_eq_priority original_job_cost next_suspension sched_susp) j_hp t
  · have BACKhp : backlogged job_arrival (inflated_job_cost original_job_cost next_suspension) (sched_new job_arrival arr_seq higher_eq_priority original_job_cost next_suspension sched_susp) j_hp t = true := by
      simp only [backlogged, PENDhp', SCHEDhp', Bool.not_false, Bool.and_self]
    have HP' := sched_new_respects_policy job_arrival arr_seq H_arrival_times_are_consistent higher_eq_priority H_priority_is_transitive H_priority_is_total original_job_cost next_suspension sched_susp j_hp j t
      H_j_hp_comes_from_sequence BACKhp H_j_scheduled_in_new
    have SAME := sched_new_breaks_ties job_arrival arr_seq H_arrival_times_are_consistent higher_eq_priority original_job_cost next_suspension sched_susp j_hp j t H_higher_or_equal_priority HP'
      H_j_hp_is_scheduled PENDhp' H_j_scheduled_in_new
    subst SAME
    rw [H_j_scheduled_in_new] at SCHEDhp'; exact absurd SCHEDhp' (by simp)
  · have SAME := only_one_job_scheduled (sched_new job_arrival arr_seq higher_eq_priority original_job_cost next_suspension sched_susp) j j_hp t H_j_scheduled_in_new SCHEDhp'
    subst SAME
    rw [H_j_hp_is_scheduled] at H_j_not_scheduled_in_susp; exact absurd H_j_not_scheduled_in_susp (by simp)

theorem reduction_inductive_step_j_hp_completed_in_susp {Job : Type v} [DecidableEq Job] (job_arrival : Job → time) (arr_seq : arrival_sequence Job) (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq) (higher_eq_priority : JLDP_policy Job) (H_priority_is_transitive : JLDP_is_transitive higher_eq_priority)
    (H_priority_is_total : JLDP_is_total arr_seq higher_eq_priority) (original_job_cost : Job → time) (next_suspension : job_suspension Job) (sched_susp : schedule Job)
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched_susp)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute original_job_cost sched_susp) (H_respects_self_suspensions : respects_self_suspensions job_arrival original_job_cost next_suspension sched_susp) (t : time) (H_induction_hypothesis : ∀ j, arrives_in arr_seq j →
      service (sched_new job_arrival arr_seq higher_eq_priority original_job_cost next_suspension sched_susp) j t ≤ service sched_susp j t + cumulative_suspension job_arrival original_job_cost next_suspension sched_susp j t) (j : Job)
    (H_comes_from_arrival_sequence : arrives_in arr_seq j)
    (H_j_has_arrived : has_arrived job_arrival j t = true)
    (H_j_is_pending : (!completed_by original_job_cost sched_susp j t) = true)
    (H_j_scheduled_in_new : scheduled_at (sched_new job_arrival arr_seq higher_eq_priority original_job_cost next_suspension sched_susp) j t = true)
    (H_j_not_scheduled_in_susp : (!scheduled_at sched_susp j t) = true)
    (H_j_is_not_suspended : (!suspended_at job_arrival original_job_cost next_suspension sched_susp j t) = true)
    (j_hp : Job) (H_j_hp_comes_from_sequence : arrives_in arr_seq j_hp)
    (H_j_hp_is_scheduled : scheduled_at sched_susp j_hp t = true)
    (H_higher_or_equal_priority : higher_eq_priority t j_hp j = true) :
    completed_by original_job_cost sched_susp j_hp t = true := by
  have COMPNEW := reduction_inductive_step_j_hp_completed_in_new job_arrival arr_seq H_arrival_times_are_consistent higher_eq_priority H_priority_is_transitive H_priority_is_total original_job_cost next_suspension sched_susp
    H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute t j H_comes_from_arrival_sequence H_j_has_arrived H_j_is_pending H_j_scheduled_in_new
      H_j_not_scheduled_in_susp H_j_is_not_suspended j_hp H_j_hp_comes_from_sequence H_j_hp_is_scheduled
      H_higher_or_equal_priority
  have IHt := H_induction_hypothesis j_hp H_j_hp_comes_from_sequence
  have LEtot := cumulative_suspension_le_total_suspension job_arrival original_job_cost next_suspension sched_susp
    H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_respects_self_suspensions j_hp 0 t
  have C1 := of_decide_eq_true COMPNEW
  unfold inflated_job_cost at C1
  unfold cumulative_suspension at IHt
  exact decide_eq_true (by omega')

theorem reduction_inductive_step_contradiction {Job : Type v} [DecidableEq Job] (job_arrival : Job → time) (arr_seq : arrival_sequence Job) (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq) (higher_eq_priority : JLDP_policy Job) (H_priority_is_transitive : JLDP_is_transitive higher_eq_priority)
    (H_priority_is_total : JLDP_is_total arr_seq higher_eq_priority) (original_job_cost : Job → time) (next_suspension : job_suspension Job) (sched_susp : schedule Job)
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched_susp)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute original_job_cost sched_susp) (H_respects_self_suspensions : respects_self_suspensions job_arrival original_job_cost next_suspension sched_susp) (t : time) (H_induction_hypothesis : ∀ j, arrives_in arr_seq j →
      service (sched_new job_arrival arr_seq higher_eq_priority original_job_cost next_suspension sched_susp) j t ≤ service sched_susp j t + cumulative_suspension job_arrival original_job_cost next_suspension sched_susp j t) (j : Job)
    (H_comes_from_arrival_sequence : arrives_in arr_seq j)
    (H_j_has_arrived : has_arrived job_arrival j t = true)
    (H_j_is_pending : (!completed_by original_job_cost sched_susp j t) = true)
    (H_j_scheduled_in_new : scheduled_at (sched_new job_arrival arr_seq higher_eq_priority original_job_cost next_suspension sched_susp) j t = true)
    (H_j_not_scheduled_in_susp : (!scheduled_at sched_susp j t) = true)
    (H_j_is_not_suspended : (!suspended_at job_arrival original_job_cost next_suspension sched_susp j t) = true)
    (j_hp : Job) (H_j_hp_comes_from_sequence : arrives_in arr_seq j_hp)
    (H_j_hp_is_scheduled : scheduled_at sched_susp j_hp t = true)
    (H_higher_or_equal_priority : higher_eq_priority t j_hp j = true) : False := by
  have COMPhp := reduction_inductive_step_j_hp_completed_in_susp job_arrival arr_seq H_arrival_times_are_consistent higher_eq_priority H_priority_is_transitive H_priority_is_total original_job_cost next_suspension sched_susp
    H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_respects_self_suspensions t H_induction_hypothesis
    j H_comes_from_arrival_sequence H_j_has_arrived H_j_is_pending H_j_scheduled_in_new
      H_j_not_scheduled_in_susp H_j_is_not_suspended j_hp H_j_hp_comes_from_sequence H_j_hp_is_scheduled
      H_higher_or_equal_priority
  have := completed_implies_not_scheduled original_job_cost sched_susp j_hp H_completed_jobs_dont_execute t COMPhp
  rw [H_j_hp_is_scheduled] at this; exact absurd this (by simp)

theorem reduction_inductive_step_case2_pending {Job : Type v} [DecidableEq Job] (job_arrival : Job → time) (arr_seq : arrival_sequence Job) (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq) (higher_eq_priority : JLDP_policy Job) (H_priority_is_transitive : JLDP_is_transitive higher_eq_priority)
    (H_priority_is_total : JLDP_is_total arr_seq higher_eq_priority) (original_job_cost : Job → time) (next_suspension : job_suspension Job) (sched_susp : schedule Job)
    (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched_susp arr_seq) (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched_susp)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute original_job_cost sched_susp) (H_work_conserving : susp_aware.work_conserving job_arrival original_job_cost next_suspension arr_seq sched_susp)
    (H_respects_priority : susp_aware.respects_JLDP_policy job_arrival original_job_cost next_suspension arr_seq
      sched_susp higher_eq_priority) (H_respects_self_suspensions : respects_self_suspensions job_arrival original_job_cost next_suspension sched_susp) (t : time) (H_induction_hypothesis : ∀ j, arrives_in arr_seq j →
      service (sched_new job_arrival arr_seq higher_eq_priority original_job_cost next_suspension sched_susp) j t ≤ service sched_susp j t + cumulative_suspension job_arrival original_job_cost next_suspension sched_susp j t) (j : Job)
    (H_comes_from_arrival_sequence : arrives_in arr_seq j)
    (H_j_has_arrived : has_arrived job_arrival j t = true)
    (H_j_is_pending : (!completed_by original_job_cost sched_susp j t) = true) :
    service (sched_new job_arrival arr_seq higher_eq_priority original_job_cost next_suspension sched_susp) j (t + 1) ≤ service sched_susp j (t + 1) + cumulative_suspension job_arrival original_job_cost next_suspension sched_susp j (t + 1) := by
  have IHt := H_induction_hypothesis j H_comes_from_arrival_sequence
  have KEY : (scheduled_at (sched_new job_arrival arr_seq higher_eq_priority original_job_cost next_suspension sched_susp) j t).toNat ≤
      (suspended_at job_arrival original_job_cost next_suspension sched_susp j t).toNat + (scheduled_at sched_susp j t).toNat := by
    cases SCHEDn : scheduled_at (sched_new job_arrival arr_seq higher_eq_priority original_job_cost next_suspension sched_susp) j t
    · simp
    · cases SCHEDs : scheduled_at sched_susp j t
      · cases SUSP : suspended_at job_arrival original_job_cost next_suspension sched_susp j t
        · exfalso
          have NOTSCHEDs : (!scheduled_at sched_susp j t) = true := by simp [SCHEDs]
          have NOTSUSP : (!suspended_at job_arrival original_job_cost next_suspension sched_susp j t) = true := by simp [SUSP]
          obtain ⟨j_hp, INhp, SCHEDhp, HP⟩ := reduction_inductive_step_exists_hep_job job_arrival arr_seq
            higher_eq_priority original_job_cost next_suspension sched_susp H_jobs_come_from_arrival_sequence
            H_work_conserving H_respects_priority t j H_comes_from_arrival_sequence H_j_has_arrived H_j_is_pending
            NOTSCHEDs NOTSUSP
          exact reduction_inductive_step_contradiction job_arrival arr_seq H_arrival_times_are_consistent higher_eq_priority H_priority_is_transitive H_priority_is_total original_job_cost next_suspension sched_susp
            H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_respects_self_suspensions t
            H_induction_hypothesis j H_comes_from_arrival_sequence H_j_has_arrived H_j_is_pending SCHEDn NOTSCHEDs
            NOTSUSP j_hp INhp SCHEDhp HP
        · simp [SCHEDn, SCHEDs, SUSP]
      · simp [SCHEDn, SCHEDs]
  have S1 : service (sched_new job_arrival arr_seq higher_eq_priority original_job_cost next_suspension sched_susp) j (t + 1) = service (sched_new job_arrival arr_seq higher_eq_priority original_job_cost next_suspension sched_susp) j t + (scheduled_at (sched_new job_arrival arr_seq higher_eq_priority original_job_cost next_suspension sched_susp) j t).toNat := by
    unfold service service_during
    rw [Finset.sum_Ico_succ_top (Nat.zero_le _)]; rfl
  have S2 : service sched_susp j (t + 1) = service sched_susp j t + (scheduled_at sched_susp j t).toNat := by
    unfold service service_during
    rw [Finset.sum_Ico_succ_top (Nat.zero_le _)]; rfl
  have S3 : cumulative_suspension job_arrival original_job_cost next_suspension sched_susp j (t + 1) = cumulative_suspension job_arrival original_job_cost next_suspension sched_susp j t + (suspended_at job_arrival original_job_cost next_suspension sched_susp j t).toNat := by
    unfold cumulative_suspension cumulative_suspension_during
    rw [Finset.sum_Ico_succ_top (Nat.zero_le _)]
  rw [S1, S2, S3]
  omega'

theorem suspension_oblivious_preserves_service {Job : Type v} [DecidableEq Job] (job_arrival : Job → time) (arr_seq : arrival_sequence Job) (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq) (higher_eq_priority : JLDP_policy Job) (H_priority_is_transitive : JLDP_is_transitive higher_eq_priority)
    (H_priority_is_total : JLDP_is_total arr_seq higher_eq_priority) (original_job_cost : Job → time) (next_suspension : job_suspension Job) (sched_susp : schedule Job)
    (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched_susp arr_seq) (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched_susp)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute original_job_cost sched_susp) (H_work_conserving : susp_aware.work_conserving job_arrival original_job_cost next_suspension arr_seq sched_susp)
    (H_respects_priority : susp_aware.respects_JLDP_policy job_arrival original_job_cost next_suspension arr_seq
      sched_susp higher_eq_priority) (H_respects_self_suspensions : respects_self_suspensions job_arrival original_job_cost next_suspension sched_susp) :
    ∀ j t, arrives_in arr_seq j →
      service (sched_new job_arrival arr_seq higher_eq_priority original_job_cost next_suspension sched_susp) j t ≤ service sched_susp j t + cumulative_suspension job_arrival original_job_cost next_suspension sched_susp j t := by
  intro j t
  induction t generalizing j with
  | zero => intro _; simp [service, service_during]
  | succ t IHt =>
    intro ARRj
    cases ARR : has_arrived job_arrival j t
    · exact reduction_inductive_step_not_arrived job_arrival arr_seq H_arrival_times_are_consistent higher_eq_priority original_job_cost next_suspension sched_susp t j (by simp [ARR])
    · cases COMP : completed_by original_job_cost sched_susp j t
      · exact reduction_inductive_step_case2_pending job_arrival arr_seq H_arrival_times_are_consistent higher_eq_priority H_priority_is_transitive H_priority_is_total original_job_cost next_suspension sched_susp
          H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
          H_work_conserving H_respects_priority H_respects_self_suspensions t IHt j ARRj ARR (by simp [COMP])
      · exact reduction_inductive_step_case1_completed job_arrival arr_seq H_arrival_times_are_consistent higher_eq_priority original_job_cost next_suspension sched_susp
          H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_respects_self_suspensions t j COMP

theorem suspension_oblivious_preserves_completion {Job : Type v} [DecidableEq Job] (job_arrival : Job → time) (arr_seq : arrival_sequence Job) (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq) (higher_eq_priority : JLDP_policy Job) (H_priority_is_transitive : JLDP_is_transitive higher_eq_priority)
    (H_priority_is_total : JLDP_is_total arr_seq higher_eq_priority) (original_job_cost : Job → time) (next_suspension : job_suspension Job) (sched_susp : schedule Job)
    (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched_susp arr_seq) (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched_susp)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute original_job_cost sched_susp) (H_work_conserving : susp_aware.work_conserving job_arrival original_job_cost next_suspension arr_seq sched_susp)
    (H_respects_priority : susp_aware.respects_JLDP_policy job_arrival original_job_cost next_suspension arr_seq
      sched_susp higher_eq_priority) (H_respects_self_suspensions : respects_self_suspensions job_arrival original_job_cost next_suspension sched_susp) :
    ∀ j t, arrives_in arr_seq j →
      completed_by (inflated_job_cost original_job_cost next_suspension) (sched_new job_arrival arr_seq higher_eq_priority original_job_cost next_suspension sched_susp) j t = true → completed_by original_job_cost sched_susp j t = true := by
  intro j t ARRj COMPLETED
  have SERV := suspension_oblivious_preserves_service job_arrival arr_seq H_arrival_times_are_consistent higher_eq_priority H_priority_is_transitive H_priority_is_total original_job_cost next_suspension sched_susp
    H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_work_conserving
    H_respects_priority H_respects_self_suspensions j t ARRj
  have LEtot := cumulative_suspension_le_total_suspension job_arrival original_job_cost next_suspension sched_susp
    H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_respects_self_suspensions j 0 t
  have C1 := of_decide_eq_true COMPLETED
  unfold inflated_job_cost at C1
  unfold cumulative_suspension at SERV
  exact decide_eq_true (by omega')

theorem suspension_oblivious_preserves_schedulability {Job : Type v} [DecidableEq Job] (job_arrival job_deadline : Job → time)
    (arr_seq : arrival_sequence Job) (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq) (higher_eq_priority : JLDP_policy Job) (H_priority_is_transitive : JLDP_is_transitive higher_eq_priority)
    (H_priority_is_total : JLDP_is_total arr_seq higher_eq_priority) (original_job_cost : Job → time) (next_suspension : job_suspension Job) (sched_susp : schedule Job)
    (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched_susp arr_seq) (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched_susp)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute original_job_cost sched_susp) (H_work_conserving : susp_aware.work_conserving job_arrival original_job_cost next_suspension arr_seq sched_susp)
    (H_respects_priority : susp_aware.respects_JLDP_policy job_arrival original_job_cost next_suspension arr_seq
      sched_susp higher_eq_priority) (H_respects_self_suspensions : respects_self_suspensions job_arrival original_job_cost next_suspension sched_susp)
    (H_schedulable_without_suspensions : ∀ j, arrives_in arr_seq j →
      job_misses_no_deadline job_arrival (inflated_job_cost original_job_cost next_suspension) job_deadline (sched_new job_arrival arr_seq higher_eq_priority original_job_cost next_suspension sched_susp) j) :
    ∀ j, arrives_in arr_seq j → job_misses_no_deadline job_arrival original_job_cost job_deadline sched_susp j := by
  intro j ARRj
  exact suspension_oblivious_preserves_completion job_arrival arr_seq H_arrival_times_are_consistent higher_eq_priority H_priority_is_transitive H_priority_is_total original_job_cost next_suspension sched_susp
    H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_work_conserving
    H_respects_priority H_respects_self_suspensions j _ ARRj (H_schedulable_without_suspensions j ARRj)

end Prosa.Classic.Analysis.Uni.Susp.Dynamic.Oblivious.Reduction.ReductionToBasicSchedule
