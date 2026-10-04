-- Authoritative source:
-- ProsaBuddy classic Prosa (prosabuddy commit f692cb7479780cf6009493f373a309e13165201c)
-- source: classic/analysis/uni/susp/dynamic/jitter/jitter_schedule_service.v
-- sha256: see Prosa-Shunqi/classic-prosa/comprehensive-classic/file_order.csv (rank 164)

import Prosa.Classic.Util.All
import Prosa.Classic.Model.Priority
import Prosa.Classic.Model.Suspension
import Prosa.Classic.Model.Arrival.Basic.Job
import Prosa.Classic.Model.Arrival.Basic.Task
import Prosa.Classic.Model.Arrival.Basic.TaskArrival
import Prosa.Classic.Model.Arrival.Basic.ArrivalSequence
import Prosa.Classic.Model.Arrival.Jitter.Job
import Prosa.Classic.Model.Schedule.Uni.Schedulability
import Prosa.Classic.Model.Schedule.Uni.Service
import Prosa.Classic.Model.Schedule.Uni.Workload
import Prosa.Classic.Model.Schedule.Uni.ResponseTime
import Prosa.Classic.Model.Schedule.Uni.Jitter.Schedule
import Prosa.Classic.Model.Schedule.Uni.Jitter.Platform
import Prosa.Classic.Model.Schedule.Uni.Susp.SuspensionIntervals
import Prosa.Classic.Model.Schedule.Uni.Susp.Schedule
import Prosa.Classic.Model.Schedule.Uni.Susp.Platform
import Prosa.Classic.Model.Schedule.Uni.Susp.ValidSchedule
import Prosa.Classic.Analysis.Uni.Susp.Dynamic.Jitter.JitterSchedule
import Prosa.Classic.Analysis.Uni.Susp.Dynamic.Jitter.JitterScheduleProperties
import Prosa.Classic.Model.Schedule.Uni.Transformation.Construction

/-!
Comparison of the service received by the analysed job before and after reducing a suspension-aware schedule to the
jitter-aware schedule of `JitterScheduleConstruction` (Rocq module `JitterScheduleService` of
`classic/analysis/uni/susp/dynamic/jitter/jitter_schedule_service.v`).

Representation notes:
* The Rocq module aliases are Lean namespace abbreviations of the accepted modules: `reduction` is
  `JitterScheduleConstruction` and `reduction_prop` is `JitterScheduleProperties`; `susp.backlogged` is the
  suspension-aware `ScheduleWithSuspensions.backlogged`.
* The section-local `Let`s are unfolded: `sched_jitter`, `inflated_job_cost` and `job_jitter` are the corresponding
  `reduction.*` definitions applied to the section variables; `arr_j` is `job_arrival j`; `actual_job_arrival` is
  `actual_arrival job_arrival job_jitter`; `job_has_actually_arrived` is `jitter_has_passed`; `arrivals` and
  `actual_arrivals` are `jobs_arrived_between arr_seq` and `actual_arrivals_between job_arrival job_jitter arr_seq`;
  `other_hep_task tsk_other` is `higher_eq_priority tsk_other (job_task j) && !decide (tsk_other = job_task j)` and
  `other_higher_eq_priority_job j_hp` is `higher_eq_priority (job_task j_hp) (job_task j) && !decide (j_hp = j)`;
  `job_response_time_in_sched_susp_bounded_by`, `job_misses_no_deadline_in_sched_susp`,
  `job_completed_in_sched_jitter`/`_susp` and `job_cumulative_suspension` are the accepted
  `is_response_time_bound_of_job`, `job_misses_no_deadline`, `completed_by` and `cumulative_suspension_during`.
* `t.+1` is `t + 1`; `x != y` in proposition position is `(!decide (x = y)) = true`; `~~ b` is `(!b) = true`;
  Boolean section hypotheses are stated as `… = true`.
* Binder lists follow the Rocq contract (Rocq abstracts exactly the section hypotheses each proof script uses, so,
  e.g., `jitter_reduction_service_in_sched_susp_le_workload` holds for every `t`).
* The proofs follow the Rocq argument (the five-case analysis of Section 6-A, workload conservation and the induction
  on the interval length of Section 6-B, and the final comparison of Section 6-C). Sums over jobs and time are
  exchanged with the LEAN_HELPER `service_of_jobs_exchange`; the per-instant facts "at most one job is scheduled" are
  the LEAN_HELPER lemmas `service_at_sum_le_one`, `service_at_sum_ge_one` and `job_plus_others_le_one`. In the
  induction of Section 6-B the case split on pending higher-priority jobs is a classical case split on the
  existential (the Rocq script decides it with `has` over the actual arrivals).
-/

set_option linter.dupNamespace false
set_option linter.unusedVariables false

namespace Prosa.Classic.Analysis.Uni.Susp.Dynamic.Jitter.JitterScheduleService.JitterScheduleService

open Prosa.Classic.Model.Time.Time
open Prosa.Classic.Model.Arrival.Basic.ArrivalSequence.ArrivalSequence
open Prosa.Classic.Model.Arrival.Basic.Task.SporadicTaskset
open Prosa.Classic.Model.Arrival.Basic.TaskArrival.TaskArrival
open Prosa.Classic.Model.Arrival.Jitter.ArrivalSequence.ArrivalSequenceWithJitter
open Prosa.Classic.Model.Priority.Priority
open Prosa.Classic.Model.Suspension.Suspension
open Prosa.Classic.Model.Schedule.Uni.Schedule.UniprocessorSchedule hiding pending backlogged scheduled_implies_pending
open Prosa.Classic.Model.Schedule.Uni.Jitter.Schedule.UniprocessorScheduleWithJitter
open Prosa.Classic.Model.Schedule.Uni.Susp.SuspensionIntervals.SuspensionIntervals
open Prosa.Classic.Model.Schedule.Uni.Susp.ValidSchedule.ValidSuspensionAwareSchedule
open Prosa.Classic.Model.Schedule.Uni.Service.Service
open Prosa.Classic.Model.Schedule.Uni.Workload.Workload
open Prosa.Classic.Model.Schedule.Uni.ResponseTime.ResponseTime
open Prosa.Classic.Model.Schedule.Uni.Schedulability.Schedulability
open Prosa.Classic.Analysis.Uni.Susp.Dynamic.Jitter.JitterScheduleProperties.JitterScheduleProperties
open Prosa.Util.Sum (sumSeq sumFiltered)
open BigOperators

namespace reduction
export Prosa.Classic.Analysis.Uni.Susp.Dynamic.Jitter.JitterSchedule.JitterScheduleConstruction
  (inflated_job_cost job_jitter sched_jitter)
end reduction
namespace susp
export Prosa.Classic.Model.Schedule.Uni.Susp.Schedule.ScheduleWithSuspensions (backlogged)
end susp

universe u v

local macro "omega'" : tactic =>
  `(tactic| ((try dsimp only [Prosa.Classic.Model.Time.Time.time,
    Prosa.Classic.Model.Time.Time.instant, Prosa.Classic.Model.Time.Time.duration] at *) <;>
    omega))

/-! ### Definitions -/

def workload_of_other_hep_jobs_in_sched_susp {Task : Type u} [DecidableEq Task] {Job : Type v} [DecidableEq Job]
    (job_cost : Job → time) (job_task : Job → Task) (arr_seq : arrival_sequence Job)
    (higher_eq_priority : FP_policy Task) (j : Job) (t1 t2 : time) : Nat :=
  workload_of_jobs job_cost (jobs_arrived_between arr_seq t1 t2) (fun j_hp => higher_eq_priority (job_task j_hp) (job_task j) && !decide (j_hp = j))

def workload_of_other_hep_jobs_in_sched_jitter {Task : Type u} [DecidableEq Task] {Job : Type v} [DecidableEq Job]
    (job_arrival job_cost : Job → time) (job_task : Job → Task) (arr_seq : arrival_sequence Job)
    (higher_eq_priority : FP_policy Task) (job_suspension_duration : job_suspension Job) (j : Job)
    (R_hp : Job → time) (t1 t2 : time) : Nat :=
  workload_of_jobs (reduction.inflated_job_cost job_cost job_suspension_duration j) (actual_arrivals_between job_arrival (reduction.job_jitter job_arrival job_task higher_eq_priority job_cost j R_hp) arr_seq t1 t2) (fun j_hp => higher_eq_priority (job_task j_hp) (job_task j) && !decide (j_hp = j))

def service_of_other_hep_jobs_in_sched_susp {Task : Type u} [DecidableEq Task] {Job : Type v} [DecidableEq Job]
    (job_arrival : Job → time) (job_task : Job → Task) (arr_seq : arrival_sequence Job)
    (higher_eq_priority : FP_policy Task) (sched_susp : schedule Job) (j : Job) (R_j : time) (t1 t2 : time) : Nat :=
  service_of_jobs sched_susp (jobs_arrived_between arr_seq 0 (job_arrival j + R_j)) (fun j_hp => higher_eq_priority (job_task j_hp) (job_task j) && !decide (j_hp = j)) t1 t2

def service_of_other_hep_jobs_in_sched_jitter {Task : Type u} [DecidableEq Task] {Job : Type v} [DecidableEq Job]
    (job_arrival job_cost : Job → time) (job_task : Job → Task) (arr_seq : arrival_sequence Job)
    (higher_eq_priority : FP_policy Task) (job_suspension_duration : job_suspension Job) (j : Job) (R_j : time)
    (R_hp : Job → time) (t1 t2 : time) : Nat :=
  service_of_jobs (reduction.sched_jitter job_arrival job_task arr_seq higher_eq_priority job_cost job_suspension_duration j R_hp) (actual_arrivals_between job_arrival (reduction.job_jitter job_arrival job_task higher_eq_priority job_cost j R_hp) arr_seq 0 (job_arrival j + R_j)) (fun j_hp => higher_eq_priority (job_task j_hp) (job_task j) && !decide (j_hp = j)) t1 t2

/-! ### LEAN_HELPER lemmas about sums -/

/-- LEAN_HELPER: exchanging a list sum with an interval sum. -/
private theorem list_sum_finset_sum_comm {α : Type _} (L : List α) (s : Finset Nat) (f : α → Nat → Nat) :
    (L.map (fun x => ∑ t ∈ s, f x t)).sum = ∑ t ∈ s, (L.map (fun x => f x t)).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp only [List.map_cons, List.sum_cons, ih, Finset.sum_add_distrib]

/-- LEAN_HELPER: the service of a set of jobs as a sum over time of per-instant service (MathComp `exchange_big`). -/
private theorem service_of_jobs_exchange {Job : Type v} [DecidableEq Job] (sched : schedule Job) (l : List Job)
    (P : Job → Bool) (t1 t2 : time) :
    service_of_jobs sched l P t1 t2 =
      ∑ t ∈ Finset.Ico t1 t2, sumFiltered l P (fun x => service_at sched x t) := by
  unfold service_of_jobs sumFiltered service_during
  exact list_sum_finset_sum_comm _ _ _

/-- LEAN_HELPER: splitting the service of a set of jobs at an intermediate time. -/
private theorem service_of_jobs_cat {Job : Type v} [DecidableEq Job] (sched : schedule Job) (l : List Job)
    (P : Job → Bool) (t1 t2 t3 : time) (h12 : t1 ≤ t2) (h23 : t2 ≤ t3) :
    service_of_jobs sched l P t1 t2 + service_of_jobs sched l P t2 t3 = service_of_jobs sched l P t1 t3 := by
  rw [service_of_jobs_exchange, service_of_jobs_exchange, service_of_jobs_exchange]
  exact Finset.sum_Ico_consecutive _ h12 h23

/-- LEAN_HELPER: a filtered sum over a duplicate-free list is bounded by the filtered sum over a superset. -/
private theorem sumFiltered_le_of_sub {α : Type _} [DecidableEq α] (l1 l2 : List α) (P : α → Bool) (F : α → Nat)
    (h1 : l1.Nodup) (hsub : ∀ x ∈ l1, P x = true → x ∈ l2) :
    sumFiltered l1 P F ≤ sumFiltered l2 P F := by
  have := Prosa.Util.Sum.leq_sum_sub_uniq (l1.filter P) F (l2.filter P) (h1.filter _) (by
    intro x hx
    rw [List.mem_filter] at hx ⊢
    exact ⟨hsub x hx.1 hx.2, hx.2⟩)
  simpa [sumSeq, sumFiltered] using this

/-- LEAN_HELPER: terms that vanish can be dropped from a filtered sum. -/
private theorem sumFiltered_drop_zero {α : Type _} (l : List α) (P : α → Bool) (F : α → Nat) :
    sumFiltered l P F = sumFiltered l (fun x => P x && decide (0 < F x)) F := by
  unfold sumFiltered
  induction l with
  | nil => rfl
  | cons a l ih =>
    by_cases hP : P a = true
    · by_cases hF : 0 < F a
      · simp [List.filter_cons, hP, hF, ih]
      · have h0 : F a = 0 := by omega'
        simp [List.filter_cons, hP, hF, ih, h0]
    · simp [List.filter_cons, hP, ih]

/-- LEAN_HELPER: comparing filtered sums when only the non-zero terms of the first are in the second list. -/
private theorem sumFiltered_le_of_pos_sub {α : Type _} [DecidableEq α] (l1 l2 : List α) (P : α → Bool)
    (F : α → Nat) (h1 : l1.Nodup) (hsub : ∀ x ∈ l1, P x = true → 0 < F x → x ∈ l2) :
    sumFiltered l1 P F ≤ sumFiltered l2 P F := by
  rw [sumFiltered_drop_zero l1 P F]
  calc _ ≤ sumFiltered l2 (fun x => P x && decide (0 < F x)) F :=
        sumFiltered_le_of_sub l1 l2 _ F h1 (by
          intro x hx hPx
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hPx
          exact hsub x hx hPx.1 hPx.2)
    _ ≤ sumFiltered l2 P F :=
        Prosa.Util.Sum.leq_sum_seq_pred l2 F _ P (fun i _ h => by
          simp only [Bool.and_eq_true] at h
          exact h.1)

/-- LEAN_HELPER: at most one job of a duplicate-free list is scheduled at any instant. -/
private theorem service_at_sum_le_one {Job : Type v} [DecidableEq Job] (sched : schedule Job) (t : time)
    (L : List Job) (P : Job → Bool) (hL : L.Nodup) :
    sumFiltered L P (fun x => service_at sched x t) ≤ 1 := by
  unfold sumFiltered
  have hL' := hL.filter P
  generalize L.filter P = L' at hL' ⊢
  induction L' with
  | nil => simp
  | cons a L ih =>
    rw [List.nodup_cons] at hL'
    simp only [List.map_cons, List.sum_cons]
    cases hs : scheduled_at sched a t
    · have := ih hL'.2
      simp only [service_at, hs, Bool.toNat_false, Nat.zero_add]
      exact this
    · have hzero : (L.map (fun x => service_at sched x t)).sum = 0 := by
        rw [List.sum_eq_zero_iff]
        intro x hx
        obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
        have hne : y ≠ a := fun h => hL'.1 (h ▸ hy)
        cases hy' : scheduled_at sched y t
        · simp [service_at, hy']
        · exact absurd (only_one_job_scheduled sched y a t hy' hs) hne
      rw [hzero]
      simp [service_at, hs]

/-- LEAN_HELPER: a scheduled job of the list contributes one unit of service. -/
private theorem service_at_sum_ge_one {Job : Type v} [DecidableEq Job] (sched : schedule Job) (t : time)
    (L : List Job) (P : Job → Bool) (x : Job) (hx : x ∈ L) (hP : P x = true)
    (hs : scheduled_at sched x t = true) :
    1 ≤ sumFiltered L P (fun x => service_at sched x t) := by
  unfold sumFiltered
  have hmem : service_at sched x t ∈ (L.filter P).map (fun x => service_at sched x t) :=
    List.mem_map.mpr ⟨x, List.mem_filter.mpr ⟨hx, hP⟩, rfl⟩
  have h1 : service_at sched x t = 1 := by simp [service_at, hs]
  rw [← h1]
  exact List.le_sum_of_mem hmem

/-- LEAN_HELPER: a job plus the other jobs of a duplicate-free list receive at most one unit of service. -/
private theorem job_plus_others_le_one {Job : Type v} [DecidableEq Job] (sched : schedule Job) (t : time)
    (L : List Job) (P : Job → Bool) (j : Job) (hL : L.Nodup) (hj : ∀ x ∈ L, P x = true → x ≠ j) :
    service_at sched j t + sumFiltered L P (fun x => service_at sched x t) ≤ 1 := by
  cases hs : scheduled_at sched j t
  · have := service_at_sum_le_one sched t L P hL
    simp only [service_at, hs, Bool.toNat_false, Nat.zero_add]
    exact this
  · have hzero : sumFiltered L P (fun x => service_at sched x t) = 0 := by
      unfold sumFiltered
      rw [List.sum_eq_zero_iff]
      intro y hy
      obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hy
      rw [List.mem_filter] at hz
      have hne := hj z hz.1 hz.2
      cases hz' : scheduled_at sched z t
      · simp [service_at, hz']
      · exact absurd (only_one_job_scheduled sched z j t hz' hs) hne
    rw [hzero]
    simp [service_at, hs]

/-! ### Auxiliary lemmas -/

theorem jitter_reduction_service_equals_workload_in_jitter
    {Task : Type u} [DecidableEq Task]
    {Job : Type v} [DecidableEq Job]
    (job_arrival : Job → time)
    (job_cost : Job → time)
    (job_task : Job → Task)
    (arr_seq : arrival_sequence Job)
    (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq)
    (H_arrival_sequence_is_a_set : arrival_sequence_is_a_set arr_seq)
    (higher_eq_priority : FP_policy Task)
    (job_suspension_duration : job_suspension Job)
    (j : Job)
    (R_j : time)
    (R_hp : Job → time)
    (t : time)
    (H_before_end_of_interval : t ≤ job_arrival j + R_j)
    (H_workload_has_finished :
      ∀ j_hp, arrives_in arr_seq j_hp → actual_arrival_before job_arrival (reduction.job_jitter job_arrival job_task higher_eq_priority job_cost j R_hp) j_hp t = true →
        (higher_eq_priority (job_task j_hp) (job_task j) && !decide (j_hp = j)) = true →
        completed_by (reduction.inflated_job_cost job_cost job_suspension_duration j) (reduction.sched_jitter job_arrival job_task arr_seq higher_eq_priority job_cost job_suspension_duration j R_hp) j_hp t = true)
    :
    workload_of_other_hep_jobs_in_sched_jitter job_arrival job_cost job_task arr_seq higher_eq_priority job_suspension_duration j R_hp (0) (t) ≤ service_of_other_hep_jobs_in_sched_jitter job_arrival job_cost job_task arr_seq higher_eq_priority job_suspension_duration j R_j R_hp (0) (t) := by
  unfold workload_of_other_hep_jobs_in_sched_jitter service_of_other_hep_jobs_in_sched_jitter workload_of_jobs
    service_of_jobs
  calc sumFiltered (actual_arrivals_between job_arrival (reduction.job_jitter job_arrival job_task higher_eq_priority job_cost j R_hp) arr_seq (0) (t)) (fun j_hp => higher_eq_priority (job_task j_hp) (job_task j) && !decide (j_hp = j)) (reduction.inflated_job_cost job_cost job_suspension_duration j)
      ≤ sumFiltered (actual_arrivals_between job_arrival (reduction.job_jitter job_arrival job_task higher_eq_priority job_cost j R_hp) arr_seq (0) (t)) (fun j_hp => higher_eq_priority (job_task j_hp) (job_task j) && !decide (j_hp = j)) (fun j0 => service_during (reduction.sched_jitter job_arrival job_task arr_seq higher_eq_priority job_cost job_suspension_duration j R_hp) j0 0 t) := by
        apply Prosa.Util.Sum.leq_sum_seq
        intro j0 IN0 HP0
        have ARR0 := in_actual_arrivals_between_implies_arrived job_arrival (reduction.job_jitter job_arrival job_task higher_eq_priority job_cost j R_hp) arr_seq j0 0 t IN0
        have BEF0 := in_actual_arrivals_implies_arrived_before job_arrival (reduction.job_jitter job_arrival job_task higher_eq_priority job_cost j R_hp) arr_seq j0 t IN0
        exact of_decide_eq_true (H_workload_has_finished j0 ARR0 BEF0 HP0)
    _ ≤ _ := by
        apply sumFiltered_le_of_sub
        · exact actual_arrivals_uniq job_arrival (reduction.job_jitter job_arrival job_task higher_eq_priority job_cost j R_hp) arr_seq H_arrival_times_are_consistent
            H_arrival_sequence_is_a_set 0 t
        · intro x hx _
          exact actual_arrivals_between_sub job_arrival (reduction.job_jitter job_arrival job_task higher_eq_priority job_cost j R_hp) arr_seq H_arrival_times_are_consistent x 0 0 t _
            (Nat.le_refl _) H_before_end_of_interval hx

theorem jitter_reduction_service_in_sched_susp_le_workload
    {Task : Type u} [DecidableEq Task]
    {Job : Type v} [DecidableEq Job]
    (job_arrival : Job → time)
    (job_cost : Job → time)
    (job_task : Job → Task)
    (arr_seq : arrival_sequence Job)
    (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq)
    (H_arrival_sequence_is_a_set : arrival_sequence_is_a_set arr_seq)
    (higher_eq_priority : FP_policy Task)
    (job_suspension_duration : job_suspension Job)
    (sched_susp : schedule Job)
    (H_valid_schedule :
      valid_suspension_aware_schedule job_arrival arr_seq (FP_to_JLDP job_task higher_eq_priority)
        job_suspension_duration job_cost sched_susp)
    (j : Job)
    (R_j : time)
    (t : time)
    :
    service_of_other_hep_jobs_in_sched_susp job_arrival job_task arr_seq higher_eq_priority sched_susp j R_j (0) (t) ≤ workload_of_other_hep_jobs_in_sched_susp job_cost job_task arr_seq higher_eq_priority j (0) (t) := by
  have VS := H_valid_schedule
  obtain ⟨FROM, MUSTARR, COMPs, _⟩ := VS
  unfold service_of_other_hep_jobs_in_sched_susp workload_of_other_hep_jobs_in_sched_susp workload_of_jobs
  calc service_of_jobs sched_susp (jobs_arrived_between arr_seq (0) (job_arrival j + R_j)) (fun j_hp => higher_eq_priority (job_task j_hp) (job_task j) && !decide (j_hp = j)) 0 t
      ≤ service_of_jobs sched_susp (jobs_arrived_between arr_seq (0) (t)) (fun j_hp => higher_eq_priority (job_task j_hp) (job_task j) && !decide (j_hp = j)) 0 t := by
        rw [service_of_jobs_exchange, service_of_jobs_exchange]
        apply Finset.sum_le_sum
        intro t' ht'
        rw [Finset.mem_Ico] at ht'
        apply sumFiltered_le_of_pos_sub
        · exact arrivals_uniq job_arrival arr_seq H_arrival_times_are_consistent H_arrival_sequence_is_a_set _ _
        · intro x hx hP hpos
          have hs : scheduled_at sched_susp x t' = true := by
            by_contra hn
            simp only [Bool.not_eq_true] at hn
            simp [service_at, hn] at hpos
          apply arrived_between_implies_in_arrivals job_arrival arr_seq H_arrival_times_are_consistent x 0 t
            (FROM x t' hs)
          have HA : job_arrival x ≤ t' := of_decide_eq_true (MUSTARR x t' hs)
          simp only [arrived_between, Bool.and_eq_true]
          exact ⟨decide_eq_true (by omega'), decide_eq_true (by omega')⟩
    _ ≤ sumFiltered (jobs_arrived_between arr_seq (0) (t)) (fun j_hp => higher_eq_priority (job_task j_hp) (job_task j) && !decide (j_hp = j)) job_cost := by
        unfold service_of_jobs
        apply Prosa.Util.Sum.leq_sum_seq
        intro x _ _
        exact cumulative_service_le_job_cost job_cost sched_susp x COMPs 0 t

/-! ### (A) Less high-priority service before the arrival of `j` -/

theorem jitter_reduction_less_job_service_before_interval_case1
    {Task : Type u} [DecidableEq Task]
    (task_period : Task → time)
    (task_deadline : Task → time)
    {Job : Type v} [DecidableEq Job]
    (job_arrival : Job → time)
    (job_cost : Job → time)
    (job_deadline : Job → time)
    (job_task : Job → Task)
    (ts : List Task)
    (arr_seq : arrival_sequence Job)
    (H_jobs_from_taskset : ∀ j, arrives_in arr_seq j → job_task j ∈ ts)
    (H_job_deadlines_equal_task_deadlines :
      ∀ j, arrives_in arr_seq j → job_deadline j = task_deadline (job_task j))
    (H_constrained_deadlines : constrained_deadline_model task_period task_deadline ts)
    (H_sporadic_arrivals : sporadic_task_model task_period job_arrival job_task arr_seq)
    (higher_eq_priority : FP_policy Task)
    (job_suspension_duration : job_suspension Job)
    (sched_susp : schedule Job)
    (H_valid_schedule :
      valid_suspension_aware_schedule job_arrival arr_seq (FP_to_JLDP job_task higher_eq_priority)
        job_suspension_duration job_cost sched_susp)
    (j : Job)
    (H_from_arrival_sequence : arrives_in arr_seq j)
    (R_hp : Job → time)
    (H_no_deadline_misses_for_previous_jobs :
      ∀ j0, arrives_in arr_seq j0 → job_arrival j0 < job_arrival j → job_task j0 = job_task j →
        job_misses_no_deadline job_arrival job_cost job_deadline sched_susp j0)
    (j_hp : Job)
    (H_arrives : arrives_in arr_seq j_hp)
    (H_higher_or_equal_priority :
      (higher_eq_priority (job_task j_hp) (job_task j) && !decide (j_hp = j)) = true)
    (H_same_task : job_task j_hp = job_task j)
    :
    service (reduction.sched_jitter job_arrival job_task arr_seq higher_eq_priority job_cost job_suspension_duration j R_hp) j_hp (job_arrival j) ≤ service sched_susp j_hp (job_arrival j) := by
  have HEP := H_higher_or_equal_priority
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at HEP
  obtain ⟨HP, NEQ⟩ := HEP
  have AFTERj := sched_jitter_jobs_execute_after_jitter job_arrival job_task arr_seq higher_eq_priority job_cost
    job_suspension_duration j H_from_arrival_sequence R_hp
  rcases Nat.lt_or_ge (job_arrival j_hp) (job_arrival j) with BEFORE | AFTER
  · have hle := cumulative_service_le_job_cost _ _ j_hp (sched_jitter_completed_jobs_dont_execute job_arrival job_task
      arr_seq higher_eq_priority job_cost job_suspension_duration j R_hp) 0 (job_arrival j)
    have hIC : (reduction.inflated_job_cost job_cost job_suspension_duration j) j_hp = job_cost j_hp := by simp [reduction.inflated_job_cost, NEQ]
    have NOMISS := H_no_deadline_misses_for_previous_jobs j_hp H_arrives BEFORE H_same_task
    unfold job_misses_no_deadline at NOMISS
    have hD := H_job_deadlines_equal_task_deadlines j_hp H_arrives
    have hDP := H_constrained_deadlines (job_task j_hp) (H_jobs_from_taskset j_hp H_arrives)
    have SPO := H_sporadic_arrivals j_hp j NEQ H_arrives H_from_arrival_sequence H_same_task (Nat.le_of_lt BEFORE)
    have COMP := completion_monotonic job_cost sched_susp j_hp _ (job_arrival j) (by rw [hD]; omega') NOMISS
    have COMP2 : job_cost j_hp ≤ service sched_susp j_hp (job_arrival j) := of_decide_eq_true COMP
    unfold service at COMP2 ⊢
    rw [hIC] at hle
    omega'
  · have hJ : (reduction.job_jitter job_arrival job_task higher_eq_priority job_cost j R_hp) j_hp = 0 := by simp [reduction.job_jitter, H_same_task]
    have := cumulative_service_before_jitter_is_zero job_arrival (reduction.job_jitter job_arrival job_task higher_eq_priority job_cost j R_hp) (reduction.sched_jitter job_arrival job_task arr_seq higher_eq_priority job_cost job_suspension_duration j R_hp) AFTERj j_hp 0 (job_arrival j)
      (by unfold actual_arrival; rw [hJ]; omega')
    unfold service service_during
    rw [this]
    exact Nat.zero_le _

theorem jitter_reduction_less_job_service_before_interval_case2
    {Task : Type u} [DecidableEq Task]
    {Job : Type v} [DecidableEq Job]
    (job_arrival : Job → time)
    (job_cost : Job → time)
    (job_task : Job → Task)
    (arr_seq : arrival_sequence Job)
    (higher_eq_priority : FP_policy Task)
    (job_suspension_duration : job_suspension Job)
    (sched_susp : schedule Job)
    (j : Job)
    (H_from_arrival_sequence : arrives_in arr_seq j)
    (R_hp : Job → time)
    (j_hp : Job)
    (H_higher_or_equal_priority :
      (higher_eq_priority (job_task j_hp) (job_task j) && !decide (j_hp = j)) = true)
    (H_released_no_earlier : job_arrival j ≤ actual_arrival job_arrival (reduction.job_jitter job_arrival job_task higher_eq_priority job_cost j R_hp) j_hp)
    :
    service (reduction.sched_jitter job_arrival job_task arr_seq higher_eq_priority job_cost job_suspension_duration j R_hp) j_hp (job_arrival j) ≤ service sched_susp j_hp (job_arrival j) := by
  have AFTERj := sched_jitter_jobs_execute_after_jitter job_arrival job_task arr_seq higher_eq_priority job_cost
    job_suspension_duration j H_from_arrival_sequence R_hp
  have := cumulative_service_before_jitter_is_zero job_arrival (reduction.job_jitter job_arrival job_task higher_eq_priority job_cost j R_hp) (reduction.sched_jitter job_arrival job_task arr_seq higher_eq_priority job_cost job_suspension_duration j R_hp) AFTERj j_hp 0 (job_arrival j)
    H_released_no_earlier
  unfold service service_during
  rw [this]
  exact Nat.zero_le _

theorem jitter_reduction_less_job_service_before_interval_case3
    {Task : Type u} [DecidableEq Task]
    {Job : Type v} [DecidableEq Job]
    (job_arrival : Job → time)
    (job_cost : Job → time)
    (job_task : Job → Task)
    (arr_seq : arrival_sequence Job)
    (higher_eq_priority : FP_policy Task)
    (job_suspension_duration : job_suspension Job)
    (sched_susp : schedule Job)
    (j : Job)
    (H_from_arrival_sequence : arrives_in arr_seq j)
    (R_hp : Job → time)
    (j_hp : Job)
    (H_higher_or_equal_priority :
      (higher_eq_priority (job_task j_hp) (job_task j) && !decide (j_hp = j)) = true)
    (H_different_task : (!decide (job_task j_hp = job_task j)) = true)
    (H_distance_is_smaller : job_arrival j - job_arrival j_hp < R_hp j_hp - job_cost j_hp)
    :
    service (reduction.sched_jitter job_arrival job_task arr_seq higher_eq_priority job_cost job_suspension_duration j R_hp) j_hp (job_arrival j) ≤ service sched_susp j_hp (job_arrival j) := by
  have HEP := H_higher_or_equal_priority
  simp only [Bool.and_eq_true] at HEP
  have hJ : (reduction.job_jitter job_arrival job_task higher_eq_priority job_cost j R_hp) j_hp = job_arrival j - job_arrival j_hp := by
    simp only [reduction.job_jitter, HEP.1, H_different_task, Bool.true_and, ↓reduceIte]
    exact min_eq_left (Nat.le_of_lt H_distance_is_smaller)
  have AFTERj := sched_jitter_jobs_execute_after_jitter job_arrival job_task arr_seq higher_eq_priority job_cost
    job_suspension_duration j H_from_arrival_sequence R_hp
  have := cumulative_service_before_jitter_is_zero job_arrival (reduction.job_jitter job_arrival job_task higher_eq_priority job_cost j R_hp) (reduction.sched_jitter job_arrival job_task arr_seq higher_eq_priority job_cost job_suspension_duration j R_hp) AFTERj j_hp 0 (job_arrival j)
    (by unfold actual_arrival; rw [hJ]; omega')
  unfold service service_during
  rw [this]
  exact Nat.zero_le _

theorem jitter_reduction_less_job_service_before_interval_case4
    {Task : Type u} [DecidableEq Task]
    {Job : Type v} [DecidableEq Job]
    (job_arrival : Job → time)
    (job_cost : Job → time)
    (job_task : Job → Task)
    (arr_seq : arrival_sequence Job)
    (higher_eq_priority : FP_policy Task)
    (job_suspension_duration : job_suspension Job)
    (sched_susp : schedule Job)
    (j : Job)
    (R_hp : Job → time)
    (H_bounded_response_time_of_hp_jobs :
      ∀ j_hp, arrives_in arr_seq j_hp →
        (higher_eq_priority (job_task j_hp) (job_task j) && !decide (job_task j_hp = job_task j)) = true →
        is_response_time_bound_of_job job_arrival job_cost sched_susp j_hp (R_hp j_hp) = true)
    (j_hp : Job)
    (H_arrives : arrives_in arr_seq j_hp)
    (H_higher_or_equal_priority :
      (higher_eq_priority (job_task j_hp) (job_task j) && !decide (j_hp = j)) = true)
    (H_different_task : (!decide (job_task j_hp = job_task j)) = true)
    (H_completes_before_j_arrives : job_arrival j_hp + R_hp j_hp ≤ job_arrival j)
    :
    service (reduction.sched_jitter job_arrival job_task arr_seq higher_eq_priority job_cost job_suspension_duration j R_hp) j_hp (job_arrival j) ≤ service sched_susp j_hp (job_arrival j) := by
  have HEP := H_higher_or_equal_priority
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at HEP
  have hle := cumulative_service_le_job_cost _ _ j_hp (sched_jitter_completed_jobs_dont_execute job_arrival job_task
    arr_seq higher_eq_priority job_cost job_suspension_duration j R_hp) 0 (job_arrival j)
  have hIC : (reduction.inflated_job_cost job_cost job_suspension_duration j) j_hp = job_cost j_hp := by simp [reduction.inflated_job_cost, HEP.2]
  have RESP := H_bounded_response_time_of_hp_jobs j_hp H_arrives (by
    simp only [Bool.and_eq_true]
    exact ⟨HEP.1, H_different_task⟩)
  unfold is_response_time_bound_of_job at RESP
  have COMP := completion_monotonic job_cost sched_susp j_hp _ (job_arrival j) H_completes_before_j_arrives RESP
  have COMP2 : job_cost j_hp ≤ service sched_susp j_hp (job_arrival j) := of_decide_eq_true COMP
  unfold service at COMP2 ⊢
  rw [hIC] at hle
  omega'

theorem jitter_reduction_jitter_equals_R_minus_cost
    {Task : Type u} [DecidableEq Task]
    {Job : Type v} [DecidableEq Job]
    (job_arrival : Job → time)
    (job_cost : Job → time)
    (job_task : Job → Task)
    (higher_eq_priority : FP_policy Task)
    (j : Job)
    (R_hp : Job → time)
    (j_hp : Job)
    (H_higher_or_equal_priority :
      (higher_eq_priority (job_task j_hp) (job_task j) && !decide (j_hp = j)) = true)
    (H_different_task : (!decide (job_task j_hp = job_task j)) = true)
    (H_distance_is_not_smaller : R_hp j_hp - job_cost j_hp ≤ job_arrival j - job_arrival j_hp)
    :
    (reduction.job_jitter job_arrival job_task higher_eq_priority job_cost j R_hp) j_hp = R_hp j_hp - job_cost j_hp := by
  have HEP := H_higher_or_equal_priority
  simp only [Bool.and_eq_true] at HEP
  simp only [reduction.job_jitter, HEP.1, H_different_task, Bool.true_and, ↓reduceIte]
  exact min_eq_right H_distance_is_not_smaller

theorem jitter_reduction_less_job_service_before_interval_case5
    {Task : Type u} [DecidableEq Task]
    {Job : Type v} [DecidableEq Job]
    (job_arrival : Job → time)
    (job_cost : Job → time)
    (job_task : Job → Task)
    (arr_seq : arrival_sequence Job)
    (higher_eq_priority : FP_policy Task)
    (job_suspension_duration : job_suspension Job)
    (sched_susp : schedule Job)
    (H_valid_schedule :
      valid_suspension_aware_schedule job_arrival arr_seq (FP_to_JLDP job_task higher_eq_priority)
        job_suspension_duration job_cost sched_susp)
    (j : Job)
    (H_from_arrival_sequence : arrives_in arr_seq j)
    (R_hp : Job → time)
    (H_bounded_response_time_of_hp_jobs :
      ∀ j_hp, arrives_in arr_seq j_hp →
        (higher_eq_priority (job_task j_hp) (job_task j) && !decide (job_task j_hp = job_task j)) = true →
        is_response_time_bound_of_job job_arrival job_cost sched_susp j_hp (R_hp j_hp) = true)
    (j_hp : Job)
    (H_arrives : arrives_in arr_seq j_hp)
    (H_higher_or_equal_priority :
      (higher_eq_priority (job_task j_hp) (job_task j) && !decide (j_hp = j)) = true)
    (H_different_task : (!decide (job_task j_hp = job_task j)) = true)
    (H_released_before : actual_arrival job_arrival (reduction.job_jitter job_arrival job_task higher_eq_priority job_cost j R_hp) j_hp < job_arrival j)
    (H_j_hp_completes_after_j_arrives : job_arrival j < job_arrival j_hp + R_hp j_hp)
    (H_distance_is_not_smaller : R_hp j_hp - job_cost j_hp ≤ job_arrival j - job_arrival j_hp)
    :
    service (reduction.sched_jitter job_arrival job_task arr_seq higher_eq_priority job_cost job_suspension_duration j R_hp) j_hp (job_arrival j) ≤ service sched_susp j_hp (job_arrival j) := by
  have VS := H_valid_schedule
  obtain ⟨_, MUSTARR, COMPs, _⟩ := VS
  have HEP := H_higher_or_equal_priority
  simp only [Bool.and_eq_true] at HEP
  have JIT := jitter_reduction_jitter_equals_R_minus_cost job_arrival job_cost job_task higher_eq_priority j R_hp j_hp H_higher_or_equal_priority H_different_task H_distance_is_not_smaller
  have AFTERj := sched_jitter_jobs_execute_after_jitter job_arrival job_task arr_seq higher_eq_priority job_cost
    job_suspension_duration j H_from_arrival_sequence R_hp
  have RESP := H_bounded_response_time_of_hp_jobs j_hp H_arrives (by
    simp only [Bool.and_eq_true]
    exact ⟨HEP.1, H_different_task⟩)
  have RESP2 : job_cost j_hp ≤ service sched_susp j_hp (job_arrival j_hp + R_hp j_hp) := of_decide_eq_true RESP
  have hA : actual_arrival job_arrival (reduction.job_jitter job_arrival job_task higher_eq_priority job_cost j R_hp) j_hp = job_arrival j_hp + (R_hp j_hp - job_cost j_hp) := by
    unfold actual_arrival
    rw [JIT]
  have hJS : service (reduction.sched_jitter job_arrival job_task arr_seq higher_eq_priority job_cost job_suspension_duration j R_hp) j_hp (job_arrival j) ≤ job_arrival j - actual_arrival job_arrival (reduction.job_jitter job_arrival job_task higher_eq_priority job_cost j R_hp) j_hp := by
    unfold service service_during
    rw [ignore_service_before_jitter job_arrival (reduction.job_jitter job_arrival job_task higher_eq_priority job_cost j R_hp) (reduction.sched_jitter job_arrival job_task arr_seq higher_eq_priority job_cost job_suspension_duration j R_hp) AFTERj j_hp 0 (job_arrival j) (by
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨Nat.zero_le _, Nat.le_of_lt H_released_before⟩)]
    have := cumulative_service_le_delta (reduction.sched_jitter job_arrival job_task arr_seq higher_eq_priority job_cost job_suspension_duration j R_hp) j_hp (actual_arrival job_arrival (reduction.job_jitter job_arrival job_task higher_eq_priority job_cost j R_hp) j_hp)
      (job_arrival j - actual_arrival job_arrival (reduction.job_jitter job_arrival job_task higher_eq_priority job_cost j R_hp) j_hp)
    unfold service_during at this
    rwa [Nat.add_sub_cancel' (Nat.le_of_lt H_released_before)] at this
  have hsplit : service sched_susp j_hp (job_arrival j_hp + R_hp j_hp) =
      service sched_susp j_hp (job_arrival j) +
        service_during sched_susp j_hp (job_arrival j) (job_arrival j_hp + R_hp j_hp) := by
    unfold service service_during
    exact (Finset.sum_Ico_consecutive _ (Nat.zero_le _) (Nat.le_of_lt H_j_hp_completes_after_j_arrives)).symm
  have hlen := cumulative_service_le_delta sched_susp j_hp (job_arrival j)
    (job_arrival j_hp + R_hp j_hp - job_arrival j)
  rw [Nat.add_sub_cancel' (Nat.le_of_lt H_j_hp_completes_after_j_arrives)] at hlen
  have hsvc : service sched_susp j_hp (job_arrival j_hp + R_hp j_hp) ≤ R_hp j_hp := by
    unfold service service_during
    rw [ignore_service_before_arrival job_arrival sched_susp MUSTARR j_hp 0 _ (Nat.zero_le _)
      (Nat.le_add_right _ _)]
    have := cumulative_service_le_delta sched_susp j_hp (job_arrival j_hp) (R_hp j_hp)
    unfold service_during at this
    exact this
  have hrel := H_released_before
  have hdist := H_distance_is_not_smaller
  have hcomp := H_j_hp_completes_after_j_arrives
  omega'

theorem jitter_reduction_less_job_service_before_interval
    {Task : Type u} [DecidableEq Task]
    (task_period : Task → time)
    (task_deadline : Task → time)
    {Job : Type v} [DecidableEq Job]
    (job_arrival : Job → time)
    (job_cost : Job → time)
    (job_deadline : Job → time)
    (job_task : Job → Task)
    (ts : List Task)
    (arr_seq : arrival_sequence Job)
    (H_jobs_from_taskset : ∀ j, arrives_in arr_seq j → job_task j ∈ ts)
    (H_job_deadlines_equal_task_deadlines :
      ∀ j, arrives_in arr_seq j → job_deadline j = task_deadline (job_task j))
    (H_constrained_deadlines : constrained_deadline_model task_period task_deadline ts)
    (H_sporadic_arrivals : sporadic_task_model task_period job_arrival job_task arr_seq)
    (higher_eq_priority : FP_policy Task)
    (job_suspension_duration : job_suspension Job)
    (sched_susp : schedule Job)
    (H_valid_schedule :
      valid_suspension_aware_schedule job_arrival arr_seq (FP_to_JLDP job_task higher_eq_priority)
        job_suspension_duration job_cost sched_susp)
    (j : Job)
    (H_from_arrival_sequence : arrives_in arr_seq j)
    (R_hp : Job → time)
    (H_bounded_response_time_of_hp_jobs :
      ∀ j_hp, arrives_in arr_seq j_hp →
        (higher_eq_priority (job_task j_hp) (job_task j) && !decide (job_task j_hp = job_task j)) = true →
        is_response_time_bound_of_job job_arrival job_cost sched_susp j_hp (R_hp j_hp) = true)
    (H_no_deadline_misses_for_previous_jobs :
      ∀ j0, arrives_in arr_seq j0 → job_arrival j0 < job_arrival j → job_task j0 = job_task j →
        job_misses_no_deadline job_arrival job_cost job_deadline sched_susp j0)
    (j_hp : Job)
    (H_arrives : arrives_in arr_seq j_hp)
    (H_higher_or_equal_priority :
      (higher_eq_priority (job_task j_hp) (job_task j) && !decide (j_hp = j)) = true)
    :
    service (reduction.sched_jitter job_arrival job_task arr_seq higher_eq_priority job_cost job_suspension_duration j R_hp) j_hp (job_arrival j) ≤ service sched_susp j_hp (job_arrival j) := by
  by_cases SAME : job_task j_hp = job_task j
  · exact jitter_reduction_less_job_service_before_interval_case1 task_period task_deadline job_arrival job_cost job_deadline job_task ts arr_seq H_jobs_from_taskset H_job_deadlines_equal_task_deadlines H_constrained_deadlines H_sporadic_arrivals higher_eq_priority job_suspension_duration sched_susp H_valid_schedule j H_from_arrival_sequence R_hp H_no_deadline_misses_for_previous_jobs j_hp H_arrives H_higher_or_equal_priority SAME
  have DIFF : (!decide (job_task j_hp = job_task j)) = true := by simp [SAME]
  by_cases LEarr : job_arrival j ≤ actual_arrival job_arrival (reduction.job_jitter job_arrival job_task higher_eq_priority job_cost j R_hp) j_hp
  · exact jitter_reduction_less_job_service_before_interval_case2 job_arrival job_cost job_task arr_seq higher_eq_priority job_suspension_duration sched_susp j H_from_arrival_sequence R_hp j_hp H_higher_or_equal_priority LEarr
  by_cases LTdiff : job_arrival j - job_arrival j_hp < R_hp j_hp - job_cost j_hp
  · exact jitter_reduction_less_job_service_before_interval_case3 job_arrival job_cost job_task arr_seq higher_eq_priority job_suspension_duration sched_susp j H_from_arrival_sequence R_hp j_hp H_higher_or_equal_priority DIFF LTdiff
  by_cases LEarrj : job_arrival j_hp + R_hp j_hp ≤ job_arrival j
  · exact jitter_reduction_less_job_service_before_interval_case4 job_arrival job_cost job_task arr_seq higher_eq_priority job_suspension_duration sched_susp j R_hp H_bounded_response_time_of_hp_jobs j_hp H_arrives H_higher_or_equal_priority DIFF LEarrj
  exact jitter_reduction_less_job_service_before_interval_case5 job_arrival job_cost job_task arr_seq higher_eq_priority job_suspension_duration sched_susp H_valid_schedule j H_from_arrival_sequence R_hp H_bounded_response_time_of_hp_jobs j_hp H_arrives H_higher_or_equal_priority DIFF (Nat.lt_of_not_le LEarr) (Nat.lt_of_not_le LEarrj) (Nat.le_of_not_lt LTdiff)

theorem jitter_reduction_less_service_before_the_interval
    {Task : Type u} [DecidableEq Task]
    (task_period : Task → time)
    (task_deadline : Task → time)
    {Job : Type v} [DecidableEq Job]
    (job_arrival : Job → time)
    (job_cost : Job → time)
    (job_deadline : Job → time)
    (job_task : Job → Task)
    (ts : List Task)
    (arr_seq : arrival_sequence Job)
    (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq)
    (H_arrival_sequence_is_a_set : arrival_sequence_is_a_set arr_seq)
    (H_jobs_from_taskset : ∀ j, arrives_in arr_seq j → job_task j ∈ ts)
    (H_job_deadlines_equal_task_deadlines :
      ∀ j, arrives_in arr_seq j → job_deadline j = task_deadline (job_task j))
    (H_constrained_deadlines : constrained_deadline_model task_period task_deadline ts)
    (H_sporadic_arrivals : sporadic_task_model task_period job_arrival job_task arr_seq)
    (higher_eq_priority : FP_policy Task)
    (job_suspension_duration : job_suspension Job)
    (sched_susp : schedule Job)
    (H_valid_schedule :
      valid_suspension_aware_schedule job_arrival arr_seq (FP_to_JLDP job_task higher_eq_priority)
        job_suspension_duration job_cost sched_susp)
    (j : Job)
    (H_from_arrival_sequence : arrives_in arr_seq j)
    (R_j : time)
    (R_hp : Job → time)
    (H_bounded_response_time_of_hp_jobs :
      ∀ j_hp, arrives_in arr_seq j_hp →
        (higher_eq_priority (job_task j_hp) (job_task j) && !decide (job_task j_hp = job_task j)) = true →
        is_response_time_bound_of_job job_arrival job_cost sched_susp j_hp (R_hp j_hp) = true)
    (H_no_deadline_misses_for_previous_jobs :
      ∀ j0, arrives_in arr_seq j0 → job_arrival j0 < job_arrival j → job_task j0 = job_task j →
        job_misses_no_deadline job_arrival job_cost job_deadline sched_susp j0)
    :
    service_of_other_hep_jobs_in_sched_jitter job_arrival job_cost job_task arr_seq higher_eq_priority job_suspension_duration j R_j R_hp (0) (job_arrival j) ≤ service_of_other_hep_jobs_in_sched_susp job_arrival job_task arr_seq higher_eq_priority sched_susp j R_j (0) (job_arrival j) := by
  unfold service_of_other_hep_jobs_in_sched_jitter service_of_other_hep_jobs_in_sched_susp service_of_jobs
  calc sumFiltered (actual_arrivals_between job_arrival (reduction.job_jitter job_arrival job_task higher_eq_priority job_cost j R_hp) arr_seq (0) (job_arrival j + R_j)) (fun j_hp => higher_eq_priority (job_task j_hp) (job_task j) && !decide (j_hp = j)) (fun j0 => service_during (reduction.sched_jitter job_arrival job_task arr_seq higher_eq_priority job_cost job_suspension_duration j R_hp) j0 0 (job_arrival j))
      ≤ sumFiltered (actual_arrivals_between job_arrival (reduction.job_jitter job_arrival job_task higher_eq_priority job_cost j R_hp) arr_seq (0) (job_arrival j + R_j)) (fun j_hp => higher_eq_priority (job_task j_hp) (job_task j) && !decide (j_hp = j))
          (fun j0 => service_during sched_susp j0 0 (job_arrival j)) := by
        apply Prosa.Util.Sum.leq_sum_seq
        intro j0 IN0 HP0
        exact jitter_reduction_less_job_service_before_interval task_period task_deadline job_arrival job_cost job_deadline job_task ts arr_seq H_jobs_from_taskset H_job_deadlines_equal_task_deadlines H_constrained_deadlines H_sporadic_arrivals higher_eq_priority job_suspension_duration sched_susp H_valid_schedule j H_from_arrival_sequence R_hp H_bounded_response_time_of_hp_jobs H_no_deadline_misses_for_previous_jobs j0 (in_actual_arrivals_between_implies_arrived job_arrival _ arr_seq j0 _ _ IN0) HP0
    _ ≤ _ := by
        apply sumFiltered_le_of_sub
        · exact actual_arrivals_uniq job_arrival _ arr_seq H_arrival_times_are_consistent H_arrival_sequence_is_a_set
            _ _
        · intro x hx _
          exact (List.mem_filter.mp hx).1

/-! ### (B) More high-priority service after the arrival of `j` -/

theorem jitter_reduction_actual_arrival_before_end_of_interval
    {Task : Type u} [DecidableEq Task]
    {Job : Type v} [DecidableEq Job]
    (job_arrival : Job → time)
    (job_cost : Job → time)
    (job_task : Job → Task)
    (higher_eq_priority : FP_policy Task)
    (j : Job)
    (R_hp : Job → time)
    (t : time)
    (H_no_earlier_than_j : job_arrival j ≤ t)
    :
    ∀ j_hp : Job,
      (higher_eq_priority (job_task j_hp) (job_task j) && !decide (j_hp = j)) = true →
      job_arrival j_hp ≤ t →
      actual_arrival job_arrival (reduction.job_jitter job_arrival job_task higher_eq_priority job_cost j R_hp) j_hp ≤ t := by
  intro j_hp HEP ARRhp
  unfold actual_arrival reduction.job_jitter
  split
  · have := min_le_left (job_arrival j - job_arrival j_hp) (R_hp j_hp - job_cost j_hp)
    omega'
  · omega'

theorem jitter_reduction_workload_conservation_inside_interval
    {Task : Type u} [DecidableEq Task]
    {Job : Type v} [DecidableEq Job]
    (job_arrival : Job → time)
    (job_cost : Job → time)
    (job_task : Job → Task)
    (arr_seq : arrival_sequence Job)
    (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq)
    (H_arrival_sequence_is_a_set : arrival_sequence_is_a_set arr_seq)
    (higher_eq_priority : FP_policy Task)
    (job_suspension_duration : job_suspension Job)
    (j : Job)
    (R_hp : Job → time)
    (t : time)
    (H_no_earlier_than_j : job_arrival j ≤ t)
    :
    workload_of_other_hep_jobs_in_sched_susp job_cost job_task arr_seq higher_eq_priority j (0) (t + 1) ≤ workload_of_other_hep_jobs_in_sched_jitter job_arrival job_cost job_task arr_seq higher_eq_priority job_suspension_duration j R_hp (0) (t + 1) := by
  unfold workload_of_other_hep_jobs_in_sched_susp workload_of_other_hep_jobs_in_sched_jitter workload_of_jobs
  calc sumFiltered (jobs_arrived_between arr_seq (0) (t + 1)) (fun j_hp => higher_eq_priority (job_task j_hp) (job_task j) && !decide (j_hp = j)) job_cost
      ≤ sumFiltered (jobs_arrived_between arr_seq (0) (t + 1)) (fun j_hp => higher_eq_priority (job_task j_hp) (job_task j) && !decide (j_hp = j)) (reduction.inflated_job_cost job_cost job_suspension_duration j) := by
        apply Prosa.Util.Sum.leq_sum_seq
        intro j0 _ HP0
        simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at HP0
        simp [reduction.inflated_job_cost, HP0.2]
    _ ≤ _ := by
        apply sumFiltered_le_of_sub
        · exact arrivals_uniq job_arrival arr_seq H_arrival_times_are_consistent H_arrival_sequence_is_a_set _ _
        · intro x hx HPx
          have BEF := in_arrivals_implies_arrived_before job_arrival arr_seq H_arrival_times_are_consistent x (t + 1) hx
          have BEF2 : job_arrival x < t + 1 := of_decide_eq_true BEF
          have := jitter_reduction_actual_arrival_before_end_of_interval job_arrival job_cost job_task higher_eq_priority j R_hp t H_no_earlier_than_j x HPx (by omega')
          show x ∈ List.filter _ (jobs_arrived_before arr_seq (t + 1))
          rw [List.mem_filter]
          exact ⟨hx, by
            simp only [Bool.and_eq_true]
            exact ⟨decide_eq_true (by omega'), decide_eq_true (by omega')⟩⟩

theorem jitter_reduction_convert_service_to_workload
    {Task : Type u} [DecidableEq Task]
    {Job : Type v} [DecidableEq Job]
    (job_arrival : Job → time)
    (job_cost : Job → time)
    (job_task : Job → Task)
    (arr_seq : arrival_sequence Job)
    (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq)
    (H_arrival_sequence_is_a_set : arrival_sequence_is_a_set arr_seq)
    (higher_eq_priority : FP_policy Task)
    (job_suspension_duration : job_suspension Job)
    (sched_susp : schedule Job)
    (H_valid_schedule :
      valid_suspension_aware_schedule job_arrival arr_seq (FP_to_JLDP job_task higher_eq_priority)
        job_suspension_duration job_cost sched_susp)
    (j : Job)
    (R_j : time)
    (R_hp : Job → time)
    (d : time)
    :
    service_of_other_hep_jobs_in_sched_susp job_arrival job_task arr_seq higher_eq_priority sched_susp j R_j (job_arrival j) (job_arrival j + d + 1) ≤
      workload_of_other_hep_jobs_in_sched_susp job_cost job_task arr_seq higher_eq_priority j (0) (job_arrival j + d + 1) - service_of_other_hep_jobs_in_sched_susp job_arrival job_task arr_seq higher_eq_priority sched_susp j R_j (0) (job_arrival j) := by
  have LE := jitter_reduction_service_in_sched_susp_le_workload job_arrival job_cost job_task arr_seq H_arrival_times_are_consistent H_arrival_sequence_is_a_set higher_eq_priority job_suspension_duration sched_susp H_valid_schedule j R_j (job_arrival j + d + 1)
  have CAT : service_of_other_hep_jobs_in_sched_susp job_arrival job_task arr_seq higher_eq_priority sched_susp j R_j (0) (job_arrival j) + service_of_other_hep_jobs_in_sched_susp job_arrival job_task arr_seq higher_eq_priority sched_susp j R_j (job_arrival j) (job_arrival j + d + 1) =
      service_of_other_hep_jobs_in_sched_susp job_arrival job_task arr_seq higher_eq_priority sched_susp j R_j (0) (job_arrival j + d + 1) := by
    unfold service_of_other_hep_jobs_in_sched_susp
    exact service_of_jobs_cat _ _ _ _ _ _ (Nat.zero_le _) (by omega')
  omega'

theorem jitter_reduction_compare_workload
    {Task : Type u} [DecidableEq Task]
    {Job : Type v} [DecidableEq Job]
    (job_arrival : Job → time)
    (job_cost : Job → time)
    (job_task : Job → Task)
    (arr_seq : arrival_sequence Job)
    (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq)
    (H_arrival_sequence_is_a_set : arrival_sequence_is_a_set arr_seq)
    (higher_eq_priority : FP_policy Task)
    (job_suspension_duration : job_suspension Job)
    (sched_susp : schedule Job)
    (j : Job)
    (R_j : time)
    (R_hp : Job → time)
    (d : time)
    :
    workload_of_other_hep_jobs_in_sched_susp job_cost job_task arr_seq higher_eq_priority j (0) (job_arrival j + d + 1) - service_of_other_hep_jobs_in_sched_susp job_arrival job_task arr_seq higher_eq_priority sched_susp j R_j (0) (job_arrival j) ≤
      workload_of_other_hep_jobs_in_sched_jitter job_arrival job_cost job_task arr_seq higher_eq_priority job_suspension_duration j R_hp (0) (job_arrival j + d + 1) - service_of_other_hep_jobs_in_sched_susp job_arrival job_task arr_seq higher_eq_priority sched_susp j R_j (0) (job_arrival j) := by
  have CONS := jitter_reduction_workload_conservation_inside_interval job_arrival job_cost job_task arr_seq H_arrival_times_are_consistent H_arrival_sequence_is_a_set higher_eq_priority job_suspension_duration j R_hp (job_arrival j + d) (Nat.le_add_right _ _)
  omega'

theorem jitter_reduction_compare_service
    {Task : Type u} [DecidableEq Task]
    (task_period : Task → time)
    (task_deadline : Task → time)
    {Job : Type v} [DecidableEq Job]
    (job_arrival : Job → time)
    (job_cost : Job → time)
    (job_deadline : Job → time)
    (job_task : Job → Task)
    (ts : List Task)
    (arr_seq : arrival_sequence Job)
    (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq)
    (H_arrival_sequence_is_a_set : arrival_sequence_is_a_set arr_seq)
    (H_jobs_from_taskset : ∀ j, arrives_in arr_seq j → job_task j ∈ ts)
    (H_job_deadlines_equal_task_deadlines :
      ∀ j, arrives_in arr_seq j → job_deadline j = task_deadline (job_task j))
    (H_constrained_deadlines : constrained_deadline_model task_period task_deadline ts)
    (H_sporadic_arrivals : sporadic_task_model task_period job_arrival job_task arr_seq)
    (higher_eq_priority : FP_policy Task)
    (job_suspension_duration : job_suspension Job)
    (sched_susp : schedule Job)
    (H_valid_schedule :
      valid_suspension_aware_schedule job_arrival arr_seq (FP_to_JLDP job_task higher_eq_priority)
        job_suspension_duration job_cost sched_susp)
    (j : Job)
    (H_from_arrival_sequence : arrives_in arr_seq j)
    (R_j : time)
    (R_hp : Job → time)
    (H_bounded_response_time_of_hp_jobs :
      ∀ j_hp, arrives_in arr_seq j_hp →
        (higher_eq_priority (job_task j_hp) (job_task j) && !decide (job_task j_hp = job_task j)) = true →
        is_response_time_bound_of_job job_arrival job_cost sched_susp j_hp (R_hp j_hp) = true)
    (H_no_deadline_misses_for_previous_jobs :
      ∀ j0, arrives_in arr_seq j0 → job_arrival j0 < job_arrival j → job_task j0 = job_task j →
        job_misses_no_deadline job_arrival job_cost job_deadline sched_susp j0)
    (d : time)
    :
    workload_of_other_hep_jobs_in_sched_jitter job_arrival job_cost job_task arr_seq higher_eq_priority job_suspension_duration j R_hp (0) (job_arrival j + d + 1) - service_of_other_hep_jobs_in_sched_susp job_arrival job_task arr_seq higher_eq_priority sched_susp j R_j (0) (job_arrival j) ≤
      workload_of_other_hep_jobs_in_sched_jitter job_arrival job_cost job_task arr_seq higher_eq_priority job_suspension_duration j R_hp (0) (job_arrival j + d + 1) - service_of_other_hep_jobs_in_sched_jitter job_arrival job_cost job_task arr_seq higher_eq_priority job_suspension_duration j R_j R_hp (0) (job_arrival j) := by
  have LE := jitter_reduction_less_service_before_the_interval task_period task_deadline job_arrival job_cost job_deadline job_task ts arr_seq H_arrival_times_are_consistent H_arrival_sequence_is_a_set H_jobs_from_taskset H_job_deadlines_equal_task_deadlines H_constrained_deadlines H_sporadic_arrivals higher_eq_priority job_suspension_duration sched_susp H_valid_schedule j H_from_arrival_sequence R_j R_hp H_bounded_response_time_of_hp_jobs H_no_deadline_misses_for_previous_jobs
  omega'

theorem jitter_reduction_convert_workload_to_service
    {Task : Type u} [DecidableEq Task]
    {Job : Type v} [DecidableEq Job]
    (job_arrival : Job → time)
    (job_cost : Job → time)
    (job_task : Job → Task)
    (arr_seq : arrival_sequence Job)
    (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq)
    (H_arrival_sequence_is_a_set : arrival_sequence_is_a_set arr_seq)
    (higher_eq_priority : FP_policy Task)
    (job_suspension_duration : job_suspension Job)
    (sched_susp : schedule Job)
    (j : Job)
    (R_j : time)
    (R_hp : Job → time)
    (d : time)
    (H_d_lt_R : d < R_j)
    (H_all_jobs_completed_in_sched_jitter :
      ∀ j_hp, arrives_in arr_seq j_hp →
        (higher_eq_priority (job_task j_hp) (job_task j) && !decide (j_hp = j)) = true →
        jitter_has_passed job_arrival (reduction.job_jitter job_arrival job_task higher_eq_priority job_cost j R_hp) j_hp (job_arrival j + d) = true →
        completed_by (reduction.inflated_job_cost job_cost job_suspension_duration j) (reduction.sched_jitter job_arrival job_task arr_seq higher_eq_priority job_cost job_suspension_duration j R_hp) j_hp (job_arrival j + d) = true)
    :
    workload_of_other_hep_jobs_in_sched_jitter job_arrival job_cost job_task arr_seq higher_eq_priority job_suspension_duration j R_hp (0) (job_arrival j + d + 1) - service_of_other_hep_jobs_in_sched_jitter job_arrival job_cost job_task arr_seq higher_eq_priority job_suspension_duration j R_j R_hp (0) (job_arrival j) ≤
      service_of_other_hep_jobs_in_sched_jitter job_arrival job_cost job_task arr_seq higher_eq_priority job_suspension_duration j R_j R_hp (job_arrival j) (job_arrival j + d + 1) := by
  have WORK : ∀ j_hp, arrives_in arr_seq j_hp →
      actual_arrival_before job_arrival (reduction.job_jitter job_arrival job_task higher_eq_priority job_cost j R_hp) j_hp (job_arrival j + d + 1) = true →
      (higher_eq_priority (job_task j_hp) (job_task j) && !decide (j_hp = j)) = true →
      completed_by (reduction.inflated_job_cost job_cost job_suspension_duration j) (reduction.sched_jitter job_arrival job_task arr_seq higher_eq_priority job_cost job_suspension_duration j R_hp) j_hp (job_arrival j + d + 1) = true := by
    intro j0 ARR0 BEF0 HP0
    have B2 : actual_arrival job_arrival (reduction.job_jitter job_arrival job_task higher_eq_priority job_cost j R_hp) j0 < job_arrival j + d + 1 := of_decide_eq_true BEF0
    have := H_all_jobs_completed_in_sched_jitter j0 ARR0 HP0 (decide_eq_true (by omega'))
    exact completion_monotonic _ _ j0 _ _ (Nat.le_succ _) this
  have EQ := jitter_reduction_service_equals_workload_in_jitter job_arrival job_cost job_task arr_seq H_arrival_times_are_consistent H_arrival_sequence_is_a_set higher_eq_priority job_suspension_duration j R_j R_hp (job_arrival j + d + 1) (by omega') WORK
  have CAT : service_of_other_hep_jobs_in_sched_jitter job_arrival job_cost job_task arr_seq higher_eq_priority job_suspension_duration j R_j R_hp (0) (job_arrival j) + service_of_other_hep_jobs_in_sched_jitter job_arrival job_cost job_task arr_seq higher_eq_priority job_suspension_duration j R_j R_hp (job_arrival j) (job_arrival j + d + 1) =
      service_of_other_hep_jobs_in_sched_jitter job_arrival job_cost job_task arr_seq higher_eq_priority job_suspension_duration j R_j R_hp (0) (job_arrival j + d + 1) := by
    unfold service_of_other_hep_jobs_in_sched_jitter
    exact service_of_jobs_cat _ _ _ _ _ _ (Nat.zero_le _) (by omega')
  omega'

theorem jitter_reduction_inductive_step_case1
    {Task : Type u} [DecidableEq Task]
    (task_period : Task → time)
    (task_deadline : Task → time)
    {Job : Type v} [DecidableEq Job]
    (job_arrival : Job → time)
    (job_cost : Job → time)
    (job_deadline : Job → time)
    (job_task : Job → Task)
    (ts : List Task)
    (arr_seq : arrival_sequence Job)
    (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq)
    (H_arrival_sequence_is_a_set : arrival_sequence_is_a_set arr_seq)
    (H_jobs_from_taskset : ∀ j, arrives_in arr_seq j → job_task j ∈ ts)
    (H_job_deadlines_equal_task_deadlines :
      ∀ j, arrives_in arr_seq j → job_deadline j = task_deadline (job_task j))
    (H_constrained_deadlines : constrained_deadline_model task_period task_deadline ts)
    (H_sporadic_arrivals : sporadic_task_model task_period job_arrival job_task arr_seq)
    (higher_eq_priority : FP_policy Task)
    (job_suspension_duration : job_suspension Job)
    (sched_susp : schedule Job)
    (H_valid_schedule :
      valid_suspension_aware_schedule job_arrival arr_seq (FP_to_JLDP job_task higher_eq_priority)
        job_suspension_duration job_cost sched_susp)
    (j : Job)
    (H_from_arrival_sequence : arrives_in arr_seq j)
    (R_j : time)
    (R_hp : Job → time)
    (H_bounded_response_time_of_hp_jobs :
      ∀ j_hp, arrives_in arr_seq j_hp →
        (higher_eq_priority (job_task j_hp) (job_task j) && !decide (job_task j_hp = job_task j)) = true →
        is_response_time_bound_of_job job_arrival job_cost sched_susp j_hp (R_hp j_hp) = true)
    (H_no_deadline_misses_for_previous_jobs :
      ∀ j0, arrives_in arr_seq j0 → job_arrival j0 < job_arrival j → job_task j0 = job_task j →
        job_misses_no_deadline job_arrival job_cost job_deadline sched_susp j0)
    (d : time)
    (H_d_lt_R : d < R_j)
    (H_all_jobs_completed_in_sched_jitter :
      ∀ j_hp, arrives_in arr_seq j_hp →
        (higher_eq_priority (job_task j_hp) (job_task j) && !decide (j_hp = j)) = true →
        jitter_has_passed job_arrival (reduction.job_jitter job_arrival job_task higher_eq_priority job_cost j R_hp) j_hp (job_arrival j + d) = true →
        completed_by (reduction.inflated_job_cost job_cost job_suspension_duration j) (reduction.sched_jitter job_arrival job_task arr_seq higher_eq_priority job_cost job_suspension_duration j R_hp) j_hp (job_arrival j + d) = true)
    :
    service_of_other_hep_jobs_in_sched_susp job_arrival job_task arr_seq higher_eq_priority sched_susp j R_j (job_arrival j) (job_arrival j + d + 1) ≤ service_of_other_hep_jobs_in_sched_jitter job_arrival job_cost job_task arr_seq higher_eq_priority job_suspension_duration j R_j R_hp (job_arrival j) (job_arrival j + d + 1) := by
  have h1 := jitter_reduction_convert_service_to_workload job_arrival job_cost job_task arr_seq H_arrival_times_are_consistent H_arrival_sequence_is_a_set higher_eq_priority job_suspension_duration sched_susp H_valid_schedule j R_j R_hp d
  have h2 := jitter_reduction_compare_workload job_arrival job_cost job_task arr_seq H_arrival_times_are_consistent H_arrival_sequence_is_a_set higher_eq_priority job_suspension_duration sched_susp j R_j R_hp d
  have h3 := jitter_reduction_compare_service task_period task_deadline job_arrival job_cost job_deadline job_task ts arr_seq H_arrival_times_are_consistent H_arrival_sequence_is_a_set H_jobs_from_taskset H_job_deadlines_equal_task_deadlines H_constrained_deadlines H_sporadic_arrivals higher_eq_priority job_suspension_duration sched_susp H_valid_schedule j H_from_arrival_sequence R_j R_hp H_bounded_response_time_of_hp_jobs H_no_deadline_misses_for_previous_jobs d
  have h4 := jitter_reduction_convert_workload_to_service job_arrival job_cost job_task arr_seq H_arrival_times_are_consistent H_arrival_sequence_is_a_set higher_eq_priority job_suspension_duration sched_susp j R_j R_hp d H_d_lt_R H_all_jobs_completed_in_sched_jitter
  omega'

theorem jitter_reduction_inductive_step_case2
    {Task : Type u} [DecidableEq Task]
    {Job : Type v} [DecidableEq Job]
    (job_arrival : Job → time)
    (job_cost : Job → time)
    (job_task : Job → Task)
    (ts : List Task)
    (arr_seq : arrival_sequence Job)
    (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq)
    (H_arrival_sequence_is_a_set : arrival_sequence_is_a_set arr_seq)
    (H_jobs_from_taskset : ∀ j, arrives_in arr_seq j → job_task j ∈ ts)
    (higher_eq_priority : FP_policy Task)
    (H_priority_is_reflexive : FP_is_reflexive higher_eq_priority)
    (H_priority_is_transitive : FP_is_transitive higher_eq_priority)
    (H_priority_is_total : FP_is_total_over_task_set higher_eq_priority ts)
    (job_suspension_duration : job_suspension Job)
    (sched_susp : schedule Job)
    (H_valid_schedule :
      valid_suspension_aware_schedule job_arrival arr_seq (FP_to_JLDP job_task higher_eq_priority)
        job_suspension_duration job_cost sched_susp)
    (j : Job)
    (H_from_arrival_sequence : arrives_in arr_seq j)
    (R_j : time)
    (R_hp : Job → time)
    (d : time)
    (H_d_lt_R : d < R_j)
    (H_induction_hypothesis :
      service_of_other_hep_jobs_in_sched_susp job_arrival job_task arr_seq higher_eq_priority sched_susp j R_j (job_arrival j) (job_arrival j + d) ≤ service_of_other_hep_jobs_in_sched_jitter job_arrival job_cost job_task arr_seq higher_eq_priority job_suspension_duration j R_j R_hp (job_arrival j) (job_arrival j + d))
    (H_there_are_pending_jobs_in_sched_jitter :
      ∃ j_hp, arrives_in arr_seq j_hp ∧
        (higher_eq_priority (job_task j_hp) (job_task j) && !decide (j_hp = j)) = true ∧
        jitter_has_passed job_arrival (reduction.job_jitter job_arrival job_task higher_eq_priority job_cost j R_hp) j_hp (job_arrival j + d) = true ∧
        (!completed_by (reduction.inflated_job_cost job_cost job_suspension_duration j) (reduction.sched_jitter job_arrival job_task arr_seq higher_eq_priority job_cost job_suspension_duration j R_hp) j_hp (job_arrival j + d)) = true)
    :
    service_of_other_hep_jobs_in_sched_susp job_arrival job_task arr_seq higher_eq_priority sched_susp j R_j (job_arrival j) (job_arrival j + d + 1) ≤ service_of_other_hep_jobs_in_sched_jitter job_arrival job_cost job_task arr_seq higher_eq_priority job_suspension_duration j R_j R_hp (job_arrival j) (job_arrival j + d + 1) := by
  have RESPj := sched_jitter_respects_policy job_arrival job_task ts arr_seq H_arrival_times_are_consistent
    H_jobs_from_taskset higher_eq_priority H_priority_is_reflexive H_priority_is_transitive H_priority_is_total
    job_cost job_suspension_duration j H_from_arrival_sequence R_hp
  have NOTj := sched_jitter_does_not_pick_j job_arrival job_task ts arr_seq H_arrival_times_are_consistent
    H_jobs_from_taskset higher_eq_priority H_priority_is_transitive H_priority_is_total job_cost
    job_suspension_duration j R_hp
  have WORKj := sched_jitter_work_conserving job_arrival job_task arr_seq H_arrival_times_are_consistent
    higher_eq_priority job_cost job_suspension_duration j R_hp
  have AFTERj := sched_jitter_jobs_execute_after_jitter job_arrival job_task arr_seq higher_eq_priority job_cost
    job_suspension_duration j H_from_arrival_sequence R_hp
  have FROMj := sched_jitter_jobs_come_from_arrival_sequence job_arrival job_task arr_seq higher_eq_priority job_cost
    job_suspension_duration sched_susp H_valid_schedule j H_from_arrival_sequence R_hp
  have CATs : service_of_other_hep_jobs_in_sched_susp job_arrival job_task arr_seq higher_eq_priority sched_susp j R_j (job_arrival j) (job_arrival j + d) + service_of_other_hep_jobs_in_sched_susp job_arrival job_task arr_seq higher_eq_priority sched_susp j R_j (job_arrival j + d) (job_arrival j + d + 1) =
      service_of_other_hep_jobs_in_sched_susp job_arrival job_task arr_seq higher_eq_priority sched_susp j R_j (job_arrival j) (job_arrival j + d + 1) := by
    unfold service_of_other_hep_jobs_in_sched_susp
    exact service_of_jobs_cat _ _ _ _ _ _ (Nat.le_add_right _ _) (Nat.le_succ _)
  have CATj : service_of_other_hep_jobs_in_sched_jitter job_arrival job_cost job_task arr_seq higher_eq_priority job_suspension_duration j R_j R_hp (job_arrival j) (job_arrival j + d) + service_of_other_hep_jobs_in_sched_jitter job_arrival job_cost job_task arr_seq higher_eq_priority job_suspension_duration j R_j R_hp (job_arrival j + d) (job_arrival j + d + 1) =
      service_of_other_hep_jobs_in_sched_jitter job_arrival job_cost job_task arr_seq higher_eq_priority job_suspension_duration j R_j R_hp (job_arrival j) (job_arrival j + d + 1) := by
    unfold service_of_other_hep_jobs_in_sched_jitter
    exact service_of_jobs_cat _ _ _ _ _ _ (Nat.le_add_right _ _) (Nat.le_succ _)
  have PTs : service_of_other_hep_jobs_in_sched_susp job_arrival job_task arr_seq higher_eq_priority sched_susp j R_j (job_arrival j + d) (job_arrival j + d + 1) =
      sumFiltered (jobs_arrived_between arr_seq (0) (job_arrival j + R_j)) (fun j_hp => higher_eq_priority (job_task j_hp) (job_task j) && !decide (j_hp = j)) (fun x => service_at sched_susp x (job_arrival j + d)) := by
    unfold service_of_other_hep_jobs_in_sched_susp
    rw [service_of_jobs_exchange, Nat.Ico_succ_singleton, Finset.sum_singleton]
  have PTj : service_of_other_hep_jobs_in_sched_jitter job_arrival job_cost job_task arr_seq higher_eq_priority job_suspension_duration j R_j R_hp (job_arrival j + d) (job_arrival j + d + 1) =
      sumFiltered (actual_arrivals_between job_arrival (reduction.job_jitter job_arrival job_task higher_eq_priority job_cost j R_hp) arr_seq (0) (job_arrival j + R_j)) (fun j_hp => higher_eq_priority (job_task j_hp) (job_task j) && !decide (j_hp = j)) (fun x => service_at (reduction.sched_jitter job_arrival job_task arr_seq higher_eq_priority job_cost job_suspension_duration j R_hp) x (job_arrival j + d)) := by
    unfold service_of_other_hep_jobs_in_sched_jitter
    rw [service_of_jobs_exchange, Nat.Ico_succ_singleton, Finset.sum_singleton]
  have LE1 := service_at_sum_le_one sched_susp (job_arrival j + d) _ (fun j_hp => higher_eq_priority (job_task j_hp) (job_task j) && !decide (j_hp = j))
    (arrivals_uniq job_arrival arr_seq H_arrival_times_are_consistent H_arrival_sequence_is_a_set 0
      (job_arrival j + R_j))
  have IH := H_induction_hypothesis
  suffices KEY : 1 ≤ sumFiltered (actual_arrivals_between job_arrival (reduction.job_jitter job_arrival job_task higher_eq_priority job_cost j R_hp) arr_seq (0) (job_arrival j + R_j)) (fun j_hp => higher_eq_priority (job_task j_hp) (job_task j) && !decide (j_hp = j))
      (fun x => service_at (reduction.sched_jitter job_arrival job_task arr_seq higher_eq_priority job_cost job_suspension_duration j R_hp) x (job_arrival j + d)) by omega'
  obtain ⟨j1, ARR1, HEP1, IN1, NOTCOMP1⟩ := H_there_are_pending_jobs_in_sched_jitter
  have HEP1' := HEP1
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at HEP1'
  obtain ⟨HP1, NEQ1⟩ := HEP1'
  have INact : ∀ x, arrives_in arr_seq x → jitter_has_passed job_arrival (reduction.job_jitter job_arrival job_task higher_eq_priority job_cost j R_hp) x (job_arrival j + d) = true →
      x ∈ actual_arrivals_between job_arrival (reduction.job_jitter job_arrival job_task higher_eq_priority job_cost j R_hp) arr_seq (0) (job_arrival j + R_j) := by
    intro x ARRx JPx
    apply arrived_between_implies_in_actual_arrivals job_arrival _ arr_seq H_arrival_times_are_consistent x 0 _ ARRx
    have JP2 : actual_arrival job_arrival (reduction.job_jitter job_arrival job_task higher_eq_priority job_cost j R_hp) x ≤ job_arrival j + d := of_decide_eq_true JPx
    have hd := H_d_lt_R
    simp only [actual_arrival_between, Bool.and_eq_true]
    exact ⟨decide_eq_true (by omega'), decide_eq_true (by omega')⟩
  cases SCHED1 : scheduled_at (reduction.sched_jitter job_arrival job_task arr_seq higher_eq_priority job_cost job_suspension_duration j R_hp) j1 (job_arrival j + d)
  · have BACK1 : backlogged job_arrival (reduction.inflated_job_cost job_cost job_suspension_duration j) (reduction.job_jitter job_arrival job_task higher_eq_priority job_cost j R_hp) (reduction.sched_jitter job_arrival job_task arr_seq higher_eq_priority job_cost job_suspension_duration j R_hp) j1 (job_arrival j + d) = true := by
      simp only [Bool.not_eq_true'] at NOTCOMP1
      simp [backlogged, pending, IN1, NOTCOMP1, SCHED1]
    obtain ⟨j2, SCHED2⟩ := WORKj j1 _ ARR1 BACK1
    have PRIO2 := RESPj j1 j2 _ ARR1 BACK1 SCHED2
    have ARR2 := FROMj j2 _ SCHED2
    have HP2 : higher_eq_priority (job_task j2) (job_task j) = true :=
      H_priority_is_transitive (job_task j1) (job_task j2) (job_task j) PRIO2 HP1
    have NE2 : j2 ≠ j := by
      intro hEQ
      rw [hEQ] at SCHED2
      have PEND1 : pending job_arrival (reduction.inflated_job_cost job_cost job_suspension_duration j) (reduction.job_jitter job_arrival job_task higher_eq_priority job_cost j R_hp) (reduction.sched_jitter job_arrival job_task arr_seq higher_eq_priority job_cost job_suspension_duration j R_hp) j1 (job_arrival j + d) = true := by
        simp only [backlogged, Bool.and_eq_true] at BACK1
        exact BACK1.1
      have := NOTj j1 _ ARR1 (by simp [NEQ1]) PEND1 HP1
      rw [SCHED2] at this
      exact Bool.noConfusion this
    exact service_at_sum_ge_one _ _ _ _ j2 (INact j2 ARR2 (AFTERj j2 _ SCHED2)) (by simp [HP2, NE2]) SCHED2
  · exact service_at_sum_ge_one _ _ _ _ j1 (INact j1 ARR1 IN1) HEP1 SCHED1

theorem jitter_reduction_more_service_inside_the_interval
    {Task : Type u} [DecidableEq Task]
    (task_period : Task → time)
    (task_deadline : Task → time)
    {Job : Type v} [DecidableEq Job]
    (job_arrival : Job → time)
    (job_cost : Job → time)
    (job_deadline : Job → time)
    (job_task : Job → Task)
    (ts : List Task)
    (arr_seq : arrival_sequence Job)
    (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq)
    (H_arrival_sequence_is_a_set : arrival_sequence_is_a_set arr_seq)
    (H_jobs_from_taskset : ∀ j, arrives_in arr_seq j → job_task j ∈ ts)
    (H_job_deadlines_equal_task_deadlines :
      ∀ j, arrives_in arr_seq j → job_deadline j = task_deadline (job_task j))
    (H_constrained_deadlines : constrained_deadline_model task_period task_deadline ts)
    (H_sporadic_arrivals : sporadic_task_model task_period job_arrival job_task arr_seq)
    (higher_eq_priority : FP_policy Task)
    (H_priority_is_reflexive : FP_is_reflexive higher_eq_priority)
    (H_priority_is_transitive : FP_is_transitive higher_eq_priority)
    (H_priority_is_total : FP_is_total_over_task_set higher_eq_priority ts)
    (job_suspension_duration : job_suspension Job)
    (sched_susp : schedule Job)
    (H_valid_schedule :
      valid_suspension_aware_schedule job_arrival arr_seq (FP_to_JLDP job_task higher_eq_priority)
        job_suspension_duration job_cost sched_susp)
    (j : Job)
    (H_from_arrival_sequence : arrives_in arr_seq j)
    (R_j : time)
    (R_hp : Job → time)
    (H_bounded_response_time_of_hp_jobs :
      ∀ j_hp, arrives_in arr_seq j_hp →
        (higher_eq_priority (job_task j_hp) (job_task j) && !decide (job_task j_hp = job_task j)) = true →
        is_response_time_bound_of_job job_arrival job_cost sched_susp j_hp (R_hp j_hp) = true)
    (H_no_deadline_misses_for_previous_jobs :
      ∀ j0, arrives_in arr_seq j0 → job_arrival j0 < job_arrival j → job_task j0 = job_task j →
        job_misses_no_deadline job_arrival job_cost job_deadline sched_susp j0)
    :
    ∀ d : time, d ≤ R_j →
      service_of_other_hep_jobs_in_sched_susp job_arrival job_task arr_seq higher_eq_priority sched_susp j R_j (job_arrival j) (job_arrival j + d) ≤ service_of_other_hep_jobs_in_sched_jitter job_arrival job_cost job_task arr_seq higher_eq_priority job_suspension_duration j R_j R_hp (job_arrival j) (job_arrival j + d) := by
  intro d
  induction d with
  | zero =>
    intro _
    simp only [Nat.add_zero]
    unfold service_of_other_hep_jobs_in_sched_susp
    rw [service_of_jobs_exchange, Finset.Ico_self, Finset.sum_empty]
    exact Nat.zero_le _
  | succ d IH =>
    intro LTR
    have IHd := IH (by omega')
    rw [Nat.succ_eq_add_one, ← Nat.add_assoc]
    by_cases HAS : ∃ j_hp, arrives_in arr_seq j_hp ∧
        (higher_eq_priority (job_task j_hp) (job_task j) && !decide (j_hp = j)) = true ∧
        jitter_has_passed job_arrival (reduction.job_jitter job_arrival job_task higher_eq_priority job_cost j R_hp) j_hp (job_arrival j + d) = true ∧
        (!completed_by (reduction.inflated_job_cost job_cost job_suspension_duration j) (reduction.sched_jitter job_arrival job_task arr_seq higher_eq_priority job_cost job_suspension_duration j R_hp) j_hp (job_arrival j + d)) = true
    · exact jitter_reduction_inductive_step_case2 job_arrival job_cost job_task ts arr_seq H_arrival_times_are_consistent H_arrival_sequence_is_a_set H_jobs_from_taskset higher_eq_priority H_priority_is_reflexive H_priority_is_transitive H_priority_is_total job_suspension_duration sched_susp H_valid_schedule j H_from_arrival_sequence R_j R_hp d (by omega') IHd HAS
    · have ALL : ∀ j_hp, arrives_in arr_seq j_hp →
          (higher_eq_priority (job_task j_hp) (job_task j) && !decide (j_hp = j)) = true →
          jitter_has_passed job_arrival (reduction.job_jitter job_arrival job_task higher_eq_priority job_cost j R_hp) j_hp (job_arrival j + d) = true →
          completed_by (reduction.inflated_job_cost job_cost job_suspension_duration j) (reduction.sched_jitter job_arrival job_task arr_seq higher_eq_priority job_cost job_suspension_duration j R_hp) j_hp (job_arrival j + d) = true := by
        intro j0 ARR0 HP0 JP0
        by_contra NC
        exact HAS ⟨j0, ARR0, HP0, JP0, by simpa using NC⟩
      exact jitter_reduction_inductive_step_case1 task_period task_deadline job_arrival job_cost job_deadline job_task ts arr_seq H_arrival_times_are_consistent H_arrival_sequence_is_a_set H_jobs_from_taskset H_job_deadlines_equal_task_deadlines H_constrained_deadlines H_sporadic_arrivals higher_eq_priority job_suspension_duration sched_susp H_valid_schedule j H_from_arrival_sequence R_j R_hp H_bounded_response_time_of_hp_jobs H_no_deadline_misses_for_previous_jobs d (by omega') ALL

/-! ### (C) The jitter-aware schedule is worse for `j` -/

theorem jitter_reduction_service_jitter
    {Task : Type u} [DecidableEq Task]
    {Job : Type v} [DecidableEq Job]
    (job_arrival : Job → time)
    (job_cost : Job → time)
    (job_task : Job → Task)
    (arr_seq : arrival_sequence Job)
    (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq)
    (H_arrival_sequence_is_a_set : arrival_sequence_is_a_set arr_seq)
    (higher_eq_priority : FP_policy Task)
    (job_suspension_duration : job_suspension Job)
    (sched_susp : schedule Job)
    (H_valid_schedule :
      valid_suspension_aware_schedule job_arrival arr_seq (FP_to_JLDP job_task higher_eq_priority)
        job_suspension_duration job_cost sched_susp)
    (j : Job)
    (H_from_arrival_sequence : arrives_in arr_seq j)
    (R_j : time)
    (R_hp : Job → time)
    :
    service_during (reduction.sched_jitter job_arrival job_task arr_seq higher_eq_priority job_cost job_suspension_duration j R_hp) j (job_arrival j) (job_arrival j + R_j) ≤
      R_j - service_of_other_hep_jobs_in_sched_jitter job_arrival job_cost job_task arr_seq higher_eq_priority job_suspension_duration j R_j R_hp (job_arrival j) (job_arrival j + R_j) := by
  have hnd := actual_arrivals_uniq job_arrival (reduction.job_jitter job_arrival job_task higher_eq_priority job_cost j R_hp) arr_seq H_arrival_times_are_consistent
    H_arrival_sequence_is_a_set 0 (job_arrival j + R_j)
  suffices H : service_during (reduction.sched_jitter job_arrival job_task arr_seq higher_eq_priority job_cost job_suspension_duration j R_hp) j (job_arrival j) (job_arrival j + R_j) +
      service_of_other_hep_jobs_in_sched_jitter job_arrival job_cost job_task arr_seq higher_eq_priority job_suspension_duration j R_j R_hp (job_arrival j) (job_arrival j + R_j) ≤ R_j by omega'
  unfold service_of_other_hep_jobs_in_sched_jitter
  rw [service_of_jobs_exchange]
  unfold service_during
  rw [← Finset.sum_add_distrib]
  calc _ ≤ ∑ _t ∈ Finset.Ico (job_arrival j) (job_arrival j + R_j), 1 := by
        apply Finset.sum_le_sum
        intro t _
        exact job_plus_others_le_one _ t _ _ j hnd (by
          intro x _ hP
          simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at hP
          exact hP.2)
    _ = R_j := by simp

theorem jitter_reduction_service_susp
    {Task : Type u} [DecidableEq Task]
    {Job : Type v} [DecidableEq Job]
    (job_arrival : Job → time)
    (job_cost : Job → time)
    (job_task : Job → Task)
    (arr_seq : arrival_sequence Job)
    (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq)
    (higher_eq_priority : FP_policy Task)
    (job_suspension_duration : job_suspension Job)
    (sched_susp : schedule Job)
    (H_valid_schedule :
      valid_suspension_aware_schedule job_arrival arr_seq (FP_to_JLDP job_task higher_eq_priority)
        job_suspension_duration job_cost sched_susp)
    (j : Job)
    (H_from_arrival_sequence : arrives_in arr_seq j)
    (R_j : time)
    (H_j_not_completed : (!completed_by job_cost sched_susp j (job_arrival j + R_j)) = true)
    :
    R_j - service_of_other_hep_jobs_in_sched_susp job_arrival job_task arr_seq higher_eq_priority sched_susp j R_j (job_arrival j) (job_arrival j + R_j) ≤
      service_during sched_susp j (job_arrival j) (job_arrival j + R_j) +
        cumulative_suspension_during job_arrival job_cost job_suspension_duration sched_susp j (job_arrival j)
          (job_arrival j + R_j) := by
  have VS := H_valid_schedule
  obtain ⟨FROM, MUSTARR, COMPs, WORK, PRIO, _⟩ := VS
  suffices H : R_j ≤ service_of_other_hep_jobs_in_sched_susp job_arrival job_task arr_seq higher_eq_priority sched_susp j R_j (job_arrival j) (job_arrival j + R_j) +
      (service_during sched_susp j (job_arrival j) (job_arrival j + R_j) +
        cumulative_suspension_during job_arrival job_cost job_suspension_duration sched_susp j (job_arrival j)
          (job_arrival j + R_j)) by omega'
  unfold service_of_other_hep_jobs_in_sched_susp
  rw [service_of_jobs_exchange]
  unfold service_during cumulative_suspension_during
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  calc R_j = ∑ _t ∈ Finset.Ico (job_arrival j) (job_arrival j + R_j), 1 := by simp
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro t ht
      rw [Finset.mem_Ico] at ht
      cases SUSP : suspended_at job_arrival job_cost job_suspension_duration sched_susp j t
      · cases SCHED : scheduled_at sched_susp j t
        · have NC : completed_by job_cost sched_susp j t = false := by
            cases hc : completed_by job_cost sched_susp j t
            · rfl
            · have := completion_monotonic job_cost sched_susp j t _ (Nat.le_of_lt ht.2) hc
              simp [this] at H_j_not_completed
          have HA : has_arrived job_arrival j t = true := decide_eq_true ht.1
          have BACK : susp.backlogged job_arrival job_cost job_suspension_duration sched_susp j t = true := by
            simp [susp.backlogged, Prosa.Classic.Model.Schedule.Uni.Schedule.UniprocessorSchedule.pending,
              HA, NC, SCHED, SUSP]
          obtain ⟨j_hp, SCHEDhp⟩ := WORK j t H_from_arrival_sequence BACK
          have HP := PRIO j j_hp t H_from_arrival_sequence BACK SCHEDhp
          simp only [FP_to_JLDP, FP_to_JLFP] at HP
          have NEQ : j_hp ≠ j := by
            rintro rfl
            rw [SCHED] at SCHEDhp
            exact Bool.noConfusion SCHEDhp
          have IN : j_hp ∈ jobs_arrived_between arr_seq (0) (job_arrival j + R_j) := by
            apply arrived_between_implies_in_arrivals job_arrival arr_seq H_arrival_times_are_consistent j_hp 0 _
              (FROM j_hp t SCHEDhp)
            have HA : job_arrival j_hp ≤ t := of_decide_eq_true (MUSTARR j_hp t SCHEDhp)
            simp only [arrived_between, Bool.and_eq_true]
            exact ⟨decide_eq_true (by omega'), decide_eq_true (by omega')⟩
          have := service_at_sum_ge_one sched_susp t _ (fun j_hp => higher_eq_priority (job_task j_hp) (job_task j) && !decide (j_hp = j)) j_hp IN (by simp [HP, NEQ]) SCHEDhp
          omega'
        · simp only [service_at, SCHED, Bool.toNat_true]
          omega'
      · simp only [SUSP, Bool.toNat_true]
        omega'

theorem jitter_reduction_less_service_for_job_j
    {Task : Type u} [DecidableEq Task]
    (task_period : Task → time)
    (task_deadline : Task → time)
    {Job : Type v} [DecidableEq Job]
    (job_arrival : Job → time)
    (job_cost : Job → time)
    (job_deadline : Job → time)
    (job_task : Job → Task)
    (ts : List Task)
    (arr_seq : arrival_sequence Job)
    (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq)
    (H_arrival_sequence_is_a_set : arrival_sequence_is_a_set arr_seq)
    (H_jobs_from_taskset : ∀ j, arrives_in arr_seq j → job_task j ∈ ts)
    (H_job_deadlines_equal_task_deadlines :
      ∀ j, arrives_in arr_seq j → job_deadline j = task_deadline (job_task j))
    (H_constrained_deadlines : constrained_deadline_model task_period task_deadline ts)
    (H_sporadic_arrivals : sporadic_task_model task_period job_arrival job_task arr_seq)
    (higher_eq_priority : FP_policy Task)
    (H_priority_is_reflexive : FP_is_reflexive higher_eq_priority)
    (H_priority_is_transitive : FP_is_transitive higher_eq_priority)
    (H_priority_is_total : FP_is_total_over_task_set higher_eq_priority ts)
    (job_suspension_duration : job_suspension Job)
    (sched_susp : schedule Job)
    (H_valid_schedule :
      valid_suspension_aware_schedule job_arrival arr_seq (FP_to_JLDP job_task higher_eq_priority)
        job_suspension_duration job_cost sched_susp)
    (j : Job)
    (H_from_arrival_sequence : arrives_in arr_seq j)
    (R_j : time)
    (R_hp : Job → time)
    (H_bounded_response_time_of_hp_jobs :
      ∀ j_hp, arrives_in arr_seq j_hp →
        (higher_eq_priority (job_task j_hp) (job_task j) && !decide (job_task j_hp = job_task j)) = true →
        is_response_time_bound_of_job job_arrival job_cost sched_susp j_hp (R_hp j_hp) = true)
    (H_no_deadline_misses_for_previous_jobs :
      ∀ j0, arrives_in arr_seq j0 → job_arrival j0 < job_arrival j → job_task j0 = job_task j →
        job_misses_no_deadline job_arrival job_cost job_deadline sched_susp j0)
    (H_j_not_completed : (!completed_by job_cost sched_susp j (job_arrival j + R_j)) = true)
    :
    service_during (reduction.sched_jitter job_arrival job_task arr_seq higher_eq_priority job_cost job_suspension_duration j R_hp) j (job_arrival j) (job_arrival j + R_j) ≤
      service_during sched_susp j (job_arrival j) (job_arrival j + R_j) +
        cumulative_suspension_during job_arrival job_cost job_suspension_duration sched_susp j (job_arrival j)
          (job_arrival j + R_j) := by
  have h1 := jitter_reduction_service_jitter job_arrival job_cost job_task arr_seq H_arrival_times_are_consistent H_arrival_sequence_is_a_set higher_eq_priority job_suspension_duration sched_susp H_valid_schedule j H_from_arrival_sequence R_j R_hp
  have h2 := jitter_reduction_more_service_inside_the_interval task_period task_deadline job_arrival job_cost job_deadline job_task ts arr_seq H_arrival_times_are_consistent H_arrival_sequence_is_a_set H_jobs_from_taskset H_job_deadlines_equal_task_deadlines H_constrained_deadlines H_sporadic_arrivals higher_eq_priority H_priority_is_reflexive H_priority_is_transitive H_priority_is_total job_suspension_duration sched_susp H_valid_schedule j H_from_arrival_sequence R_j R_hp H_bounded_response_time_of_hp_jobs H_no_deadline_misses_for_previous_jobs R_j (Nat.le_refl _)
  have h3 := jitter_reduction_service_susp job_arrival job_cost job_task arr_seq H_arrival_times_are_consistent higher_eq_priority job_suspension_duration sched_susp H_valid_schedule j H_from_arrival_sequence R_j H_j_not_completed
  omega'

theorem jitter_reduction_job_j_completes_no_later
    {Task : Type u} [DecidableEq Task]
    (task_period : Task → time)
    (task_deadline : Task → time)
    {Job : Type v} [DecidableEq Job]
    (job_arrival : Job → time)
    (job_cost : Job → time)
    (job_deadline : Job → time)
    (job_task : Job → Task)
    (ts : List Task)
    (arr_seq : arrival_sequence Job)
    (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq)
    (H_arrival_sequence_is_a_set : arrival_sequence_is_a_set arr_seq)
    (H_jobs_from_taskset : ∀ j, arrives_in arr_seq j → job_task j ∈ ts)
    (H_job_deadlines_equal_task_deadlines :
      ∀ j, arrives_in arr_seq j → job_deadline j = task_deadline (job_task j))
    (H_constrained_deadlines : constrained_deadline_model task_period task_deadline ts)
    (H_sporadic_arrivals : sporadic_task_model task_period job_arrival job_task arr_seq)
    (higher_eq_priority : FP_policy Task)
    (H_priority_is_reflexive : FP_is_reflexive higher_eq_priority)
    (H_priority_is_transitive : FP_is_transitive higher_eq_priority)
    (H_priority_is_total : FP_is_total_over_task_set higher_eq_priority ts)
    (job_suspension_duration : job_suspension Job)
    (sched_susp : schedule Job)
    (H_valid_schedule :
      valid_suspension_aware_schedule job_arrival arr_seq (FP_to_JLDP job_task higher_eq_priority)
        job_suspension_duration job_cost sched_susp)
    (j : Job)
    (H_from_arrival_sequence : arrives_in arr_seq j)
    (R_j : time)
    (R_hp : Job → time)
    (H_bounded_response_time_of_hp_jobs :
      ∀ j_hp, arrives_in arr_seq j_hp →
        (higher_eq_priority (job_task j_hp) (job_task j) && !decide (job_task j_hp = job_task j)) = true →
        is_response_time_bound_of_job job_arrival job_cost sched_susp j_hp (R_hp j_hp) = true)
    (H_no_deadline_misses_for_previous_jobs :
      ∀ j0, arrives_in arr_seq j0 → job_arrival j0 < job_arrival j → job_task j0 = job_task j →
        job_misses_no_deadline job_arrival job_cost job_deadline sched_susp j0)
    (H_response_time_of_j_in_sched_jitter :
      is_response_time_bound_of_job job_arrival (reduction.inflated_job_cost job_cost job_suspension_duration j) (reduction.sched_jitter job_arrival job_task arr_seq higher_eq_priority job_cost job_suspension_duration j R_hp) j R_j = true)
    :
    is_response_time_bound_of_job job_arrival job_cost sched_susp j R_j = true := by
  have VS := H_valid_schedule
  obtain ⟨_, MUSTARR, COMPs, _, _, SELF⟩ := VS
  by_contra NOTCOMP
  have NOTCOMP' : (!completed_by job_cost sched_susp j (job_arrival j + R_j)) = true := by
    cases h : completed_by job_cost sched_susp j (job_arrival j + R_j)
    · rfl
    · exact absurd h NOTCOMP
  have LESS := jitter_reduction_less_service_for_job_j task_period task_deadline job_arrival job_cost job_deadline job_task ts arr_seq H_arrival_times_are_consistent H_arrival_sequence_is_a_set H_jobs_from_taskset H_job_deadlines_equal_task_deadlines H_constrained_deadlines H_sporadic_arrivals higher_eq_priority H_priority_is_reflexive H_priority_is_transitive H_priority_is_total job_suspension_duration sched_susp H_valid_schedule j H_from_arrival_sequence R_j R_hp H_bounded_response_time_of_hp_jobs H_no_deadline_misses_for_previous_jobs NOTCOMP'
  have COMPj : (reduction.inflated_job_cost job_cost job_suspension_duration j) j ≤ service (reduction.sched_jitter job_arrival job_task arr_seq higher_eq_priority job_cost job_suspension_duration j R_hp) j (job_arrival j + R_j) :=
    of_decide_eq_true H_response_time_of_j_in_sched_jitter
  have hIC : (reduction.inflated_job_cost job_cost job_suspension_duration j) j = job_cost j + total_suspension job_cost job_suspension_duration j := by
    simp [reduction.inflated_job_cost]
  rw [hIC] at COMPj
  have AFTERj := sched_jitter_jobs_execute_after_jitter job_arrival job_task arr_seq higher_eq_priority job_cost
    job_suspension_duration j H_from_arrival_sequence R_hp
  have MUSTj := jobs_with_jitter_must_arrive_to_execute job_arrival (reduction.job_jitter job_arrival job_task higher_eq_priority job_cost j R_hp) (reduction.sched_jitter job_arrival job_task arr_seq higher_eq_priority job_cost job_suspension_duration j R_hp) AFTERj
  have E1 : service (reduction.sched_jitter job_arrival job_task arr_seq higher_eq_priority job_cost job_suspension_duration j R_hp) j (job_arrival j + R_j) = service_during (reduction.sched_jitter job_arrival job_task arr_seq higher_eq_priority job_cost job_suspension_duration j R_hp) j (job_arrival j) (job_arrival j + R_j) := by
    unfold service service_during
    exact ignore_service_before_arrival job_arrival _ MUSTj j 0 _ (Nat.zero_le _) (Nat.le_add_right _ _)
  have E2 : service sched_susp j (job_arrival j + R_j) =
      service_during sched_susp j (job_arrival j) (job_arrival j + R_j) := by
    unfold service service_during
    exact ignore_service_before_arrival job_arrival _ MUSTARR j 0 _ (Nat.zero_le _) (Nat.le_add_right _ _)
  have SUSPLE := cumulative_suspension_le_total_suspension job_arrival job_cost job_suspension_duration sched_susp
    MUSTARR COMPs SELF j (job_arrival j) (job_arrival j + R_j)
  have NC2 : service sched_susp j (job_arrival j + R_j) < job_cost j := by
    by_contra h
    exact NOTCOMP (decide_eq_true (Nat.le_of_not_lt h))
  omega'

end Prosa.Classic.Analysis.Uni.Susp.Dynamic.Jitter.JitterScheduleService.JitterScheduleService
