-- Authoritative source:
-- ProsaBuddy classic Prosa (prosabuddy commit f692cb7479780cf6009493f373a309e13165201c)
-- source: classic/analysis/uni/susp/sustainability/allcosts/reduction_properties.v
-- sha256: see Prosa-Shunqi/classic-prosa/comprehensive-classic/file_order.csv (rank 151)

import Prosa.Classic.Util.All
import Prosa.Classic.Model.Priority
import Prosa.Classic.Model.Suspension
import Prosa.Classic.Model.Arrival.Basic.ArrivalSequence
import Prosa.Classic.Model.Schedule.Uni.ResponseTime
import Prosa.Classic.Model.Schedule.Uni.Susp.SuspensionIntervals
import Prosa.Classic.Model.Schedule.Uni.Susp.Schedule
import Prosa.Classic.Model.Schedule.Uni.Susp.ValidSchedule
import Prosa.Classic.Model.Schedule.Uni.Susp.BuildSuspensionTable
import Prosa.Classic.Model.Schedule.Uni.Susp.Platform
import Prosa.Classic.Analysis.Uni.Susp.Sustainability.Allcosts.Reduction
import Prosa.Classic.Model.Schedule.Uni.Transformation.Construction

/-!
Properties of the schedule built in the all-costs sustainability reduction (Rocq module
`SustainabilityAllCostsProperties` of `classic/analysis/uni/susp/sustainability/allcosts/reduction_properties.v`).

Representation notes:
* The Rocq alias `reduction := SustainabilityAllCosts` is a Lean namespace abbreviation of the accepted module.
* `~~ b` is `(!b) = true`; Boolean chains `a <= b < c` in proposition position are
  `(decide (a ≤ b) && decide (b < c)) = true`.
* The section-local `Let`s (`arr_j`, `sched_new`, `suspended_in_sched_new`, `reduced_suspension_duration`,
  `job_response_time_in_sched_susp_bounded_by`, `job_response_time_in_sched_new_bounded_by`,
  `suspended_in_sched_susp`, `job_is_late`, `build_schedule`, `late_or_sched_jobs`, `hp_job`, `hp_late_job`,
  `completed_in_sched_susp`, `completed_in_sched_new`, `suspension_start` (= `time_after_last_execution job_arrival`),
  `cumulative_suspension_in_sched_susp`, `cumulative_suspension_in_sched_new`) are unfolded.
* Binder lists follow the Rocq contract (the job `any_j` of section `SuspensionPredicate` is a binder of the lemmas
  of that section).
* Proof differences (same statements): `suspended_in_sched_new_no_service_since_execution` and
  `suspended_in_sched_new_is_continuous` are proved directly from the characterization of the time after the last
  execution (the Rocq proofs use an induction whose hypothesis is not needed); the total-suspension comparison
  regroups the suspension table by instants with `Finset.sum_comm`.
-/

set_option linter.unusedVariables false

namespace Prosa.Classic.Analysis.Uni.Susp.Sustainability.Allcosts.ReductionProperties.SustainabilityAllCostsProperties

open Prosa.Classic.Model.Time.Time
open Prosa.Classic.Model.Arrival.Basic.ArrivalSequence.ArrivalSequence
open Prosa.Classic.Model.Priority.Priority
open Prosa.Classic.Model.Suspension.Suspension
open Prosa.Classic.Model.Schedule.Uni.Schedule.UniprocessorSchedule
open Prosa.Classic.Model.Schedule.Uni.ResponseTime.ResponseTime
open Prosa.Classic.Model.Schedule.Uni.Susp.LastExecution.LastExecution
open Prosa.Classic.Model.Schedule.Uni.Susp.SuspensionIntervals.SuspensionIntervals
open Prosa.Classic.Model.Schedule.Uni.Susp.Platform.PlatformWithSuspensions
open Prosa.Classic.Model.Schedule.Uni.Susp.ValidSchedule.ValidSuspensionAwareSchedule
open Prosa.Classic.Model.Schedule.Uni.Susp.BuildSuspensionTable.SuspensionTableConstruction
open Prosa.Classic.Model.Schedule.Uni.Transformation.Construction.ScheduleConstruction
open Prosa.Classic.Util.Minmax (seq_min seq_min_in_seq seq_min_exists seq_min_computes_min)
open Prosa.Util.Sum (maxFiltered)

namespace reduction
export Prosa.Classic.Analysis.Uni.Susp.Sustainability.Allcosts.Reduction.SustainabilityAllCosts
  (job_is_late jobs_that_are_late_or_scheduled_in_sched_susp highest_priority_late_job pending_jobs
   highest_priority_job build_schedule sched_new suspended_in_sched_new reduced_suspension_duration)
end reduction

universe v

local macro "omega'" : tactic =>
  `(tactic| ((try dsimp only [Prosa.Classic.Model.Time.Time.time,
    Prosa.Classic.Model.Time.Time.instant, Prosa.Classic.Model.Time.Time.duration] at *) <;>
    omega))

/-! ### Proof-local facts -/

/-- LEAN_HELPER: an element of a filtered list is bounded by the filtered maximum. -/
private theorem le_maxFiltered {α : Type _} (l : List α) (P : α → Bool) (F : α → Nat) (a : α) (ha : a ∈ l)
    (hP : P a = true) : F a ≤ maxFiltered l P F := by
  unfold maxFiltered
  have hm : F a ∈ (l.filter P).map F := List.mem_map.mpr ⟨a, List.mem_filter.mpr ⟨ha, hP⟩, rfl⟩
  generalize (l.filter P).map F = L at hm
  induction L with
  | nil => simp at hm
  | cons b L ih =>
    simp only [List.foldr_cons]
    rcases List.mem_cons.mp hm with h | h
    · rw [h]; exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih h) (Nat.le_max_right _ _)

/-- LEAN_HELPER: an execution before `t` happens before the time after the last execution. -/
private theorem lt_tale {Job : Type v} [DecidableEq Job] (job_arrival : Job → time) (sched : schedule Job) (x : Job) (t s : Nat) (hs : s < t)
    (SCHED : scheduled_at sched x s = true) : s < time_after_last_execution job_arrival sched x t := by
  have hany : (List.finRange t).any (fun t0 => scheduled_at sched x t0) = true :=
    List.any_eq_true.mpr ⟨⟨s, hs⟩, List.mem_finRange _, SCHED⟩
  unfold time_after_last_execution
  rw [if_pos hany]
  have := le_maxFiltered (List.finRange t) (fun t_last : Fin t => scheduled_at sched x t_last)
    (fun t_last : Fin t => t_last.val) ⟨s, hs⟩ (List.mem_finRange _) SCHED
  simp only at this
  omega

/-- LEAN_HELPER: without executions before `t`, the time after the last execution is the arrival time. -/
private theorem tale_none {Job : Type v} [DecidableEq Job] (job_arrival : Job → time) (sched : schedule Job) (x : Job) (t : Nat)
    (H : ∀ s, s < t → scheduled_at sched x s = false) :
    time_after_last_execution job_arrival sched x t = job_arrival x := by
  have hany : (List.finRange t).any (fun t0 => scheduled_at sched x t0) = false := by
    rw [List.any_eq_false]
    intro s _ h
    rw [H s s.isLt] at h
    exact Bool.noConfusion h
  unfold time_after_last_execution
  rw [if_neg (by simp [hany])]

private theorem service_step {Job : Type v} [DecidableEq Job] (sched : schedule Job) (x : Job) (t : Nat) :
    service sched x (t + 1) = service sched x t + (scheduled_at sched x t).toNat := by
  unfold service service_during
  rw [Finset.sum_Ico_succ_top (Nat.zero_le t)]
  rfl

private theorem service_mono {Job : Type v} [DecidableEq Job] (sched : schedule Job) (x : Job) (a b : Nat) (hab : a ≤ b) :
    service sched x a ≤ service sched x b := by
  unfold service service_during
  exact Finset.sum_le_sum_of_subset (Finset.Ico_subset_Ico (Nat.le_refl 0) hab)

/-- LEAN_HELPER: no service in an interval in which the job is not scheduled. -/
private theorem service_flat {Job : Type v} [DecidableEq Job] (sched : schedule Job) (x : Job) (a b : Nat) (hab : a ≤ b)
    (H : ∀ s, a ≤ s → s < b → scheduled_at sched x s = false) : service sched x b = service sched x a := by
  unfold service service_during
  rw [← Finset.sum_Ico_consecutive _ (Nat.zero_le a) hab]
  have : ∑ s ∈ Finset.Ico a b, service_at sched x s = 0 :=
    Finset.sum_eq_zero (fun s hs => by rw [Finset.mem_Ico] at hs; simp [service_at, H s hs.1 hs.2])
  rw [this, Nat.add_zero]

/-! ### Properties of the schedule construction -/

theorem sched_new_depends_only_on_service {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time) (arr_seq : arrival_sequence Job) (higher_eq_priority : JLDP_policy Job) (sched_susp : schedule Job) (j : Job) (R : time) (inflated_job_cost : Job → time) :
    ∀ (sched1 sched2 : schedule Job) (t : time), (∀ j, service sched1 j t = service sched2 j t) →
      reduction.build_schedule job_arrival job_cost arr_seq higher_eq_priority sched_susp inflated_job_cost j R sched1 t = reduction.build_schedule job_arrival job_cost arr_seq higher_eq_priority sched_susp inflated_job_cost j R sched2 t := by
  intro sched1 sched2 t SAME
  unfold reduction.build_schedule reduction.highest_priority_late_job reduction.highest_priority_job
    reduction.jobs_that_are_late_or_scheduled_in_sched_susp reduction.pending_jobs reduction.job_is_late
  simp only [pending, completed_by, SAME]

theorem sched_new_uses_construction_function {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time) (arr_seq : arrival_sequence Job) (higher_eq_priority : JLDP_policy Job) (sched_susp : schedule Job) (j : Job) (R : time) (inflated_job_cost : Job → time) :
    ∀ t, (reduction.sched_new job_arrival job_cost arr_seq higher_eq_priority sched_susp inflated_job_cost j R) t = reduction.build_schedule job_arrival job_cost arr_seq higher_eq_priority sched_susp inflated_job_cost j R (reduction.sched_new job_arrival job_cost arr_seq higher_eq_priority sched_susp inflated_job_cost j R) t := by
  intro t
  exact service_dependent_schedule_construction _ _ (sched_new_depends_only_on_service job_arrival job_cost arr_seq higher_eq_priority sched_susp j R inflated_job_cost) t

/-- LEAN_HELPER: facts about the job scheduled by the new schedule. -/
private theorem scheduled_facts {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time) (arr_seq : arrival_sequence Job) (higher_eq_priority : JLDP_policy Job) (sched_susp : schedule Job) (j : Job) (R : time) (inflated_job_cost : Job → time) (x : Job) (t : time) (SCHED : (reduction.sched_new job_arrival job_cost arr_seq higher_eq_priority sched_susp inflated_job_cost j R) t = some x) :
    x ∈ jobs_arrived_up_to arr_seq t ∧ pending job_arrival inflated_job_cost (reduction.sched_new job_arrival job_cost arr_seq higher_eq_priority sched_susp inflated_job_cost j R) x t = true ∧
      (t < job_arrival j + R → (reduction.job_is_late job_cost sched_susp inflated_job_cost (reduction.sched_new job_arrival job_cost arr_seq higher_eq_priority sched_susp inflated_job_cost j R) x t || scheduled_at sched_susp x t) = true) := by
  rw [sched_new_uses_construction_function job_arrival job_cost arr_seq higher_eq_priority sched_susp j R inflated_job_cost] at SCHED
  unfold reduction.build_schedule at SCHED
  split at SCHED
  · next LT =>
    have IN := seq_min_in_seq _ _ _ SCHED
    unfold reduction.jobs_that_are_late_or_scheduled_in_sched_susp at IN
    rw [List.mem_filter, Bool.and_eq_true] at IN
    exact ⟨IN.1, IN.2.1, fun _ => IN.2.2⟩
  · next GE =>
    have IN := seq_min_in_seq _ _ _ SCHED
    unfold reduction.pending_jobs at IN
    rw [List.mem_filter] at IN
    exact ⟨IN.1, IN.2, fun h => absurd h GE⟩

/-! ### Basic schedule properties -/

theorem sched_new_jobs_come_from_arrival_sequence {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time) (arr_seq : arrival_sequence Job) (higher_eq_priority : JLDP_policy Job) (sched_susp : schedule Job) (j : Job) (R : time) (inflated_job_cost : Job → time) :
    jobs_come_from_arrival_sequence (reduction.sched_new job_arrival job_cost arr_seq higher_eq_priority sched_susp inflated_job_cost j R) arr_seq := by
  intro x t SCHED
  simp only [scheduled_at, decide_eq_true_eq] at SCHED
  exact in_arrivals_implies_arrived arr_seq x 0 (t + 1) (scheduled_facts job_arrival job_cost arr_seq higher_eq_priority sched_susp j R inflated_job_cost x t SCHED).1

theorem sched_new_jobs_must_arrive_to_execute {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time) (arr_seq : arrival_sequence Job) (higher_eq_priority : JLDP_policy Job) (sched_susp : schedule Job) (j : Job) (R : time) (inflated_job_cost : Job → time) :
    jobs_must_arrive_to_execute job_arrival (reduction.sched_new job_arrival job_cost arr_seq higher_eq_priority sched_susp inflated_job_cost j R) := by
  intro x t SCHED
  simp only [scheduled_at, decide_eq_true_eq] at SCHED
  have P := (scheduled_facts job_arrival job_cost arr_seq higher_eq_priority sched_susp j R inflated_job_cost x t SCHED).2.1
  simp only [pending, Bool.and_eq_true] at P
  exact P.1

theorem sched_new_completed_jobs_dont_execute {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time) (arr_seq : arrival_sequence Job) (higher_eq_priority : JLDP_policy Job) (sched_susp : schedule Job) (j : Job) (R : time) (inflated_job_cost : Job → time) :
    completed_jobs_dont_execute inflated_job_cost (reduction.sched_new job_arrival job_cost arr_seq higher_eq_priority sched_susp inflated_job_cost j R) := by
  intro x t
  induction t with
  | zero => simp [service, service_during]
  | succ t IHt =>
    rw [service_step]
    rcases Nat.lt_or_ge (service (reduction.sched_new job_arrival job_cost arr_seq higher_eq_priority sched_susp inflated_job_cost j R) x t) (inflated_job_cost x) with LT | GE
    · have : (scheduled_at (reduction.sched_new job_arrival job_cost arr_seq higher_eq_priority sched_susp inflated_job_cost j R) x t).toNat ≤ 1 := by cases scheduled_at _ x t <;> simp
      omega'
    · have NS : scheduled_at (reduction.sched_new job_arrival job_cost arr_seq higher_eq_priority sched_susp inflated_job_cost j R) x t = false := by
        cases hs : scheduled_at (reduction.sched_new job_arrival job_cost arr_seq higher_eq_priority sched_susp inflated_job_cost j R) x t
        · rfl
        · simp only [scheduled_at, decide_eq_true_eq] at hs
          have P := (scheduled_facts job_arrival job_cost arr_seq higher_eq_priority sched_susp j R inflated_job_cost x t hs).2.1
          simp only [pending, completed_by, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at P
          exact absurd GE P.2
      simp only [NS, Bool.toNat_false, Nat.add_zero]
      exact IHt

/-! ### Service invariant -/

theorem sched_new_service_invariant {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time) (arr_seq : arrival_sequence Job) (higher_eq_priority : JLDP_policy Job) (sched_susp : schedule Job) (j : Job) (R : time) (inflated_job_cost : Job → time) (t : time) (H_before_R : t ≤ job_arrival j + R) :
    ∀ any_j, service (reduction.sched_new job_arrival job_cost arr_seq higher_eq_priority sched_susp inflated_job_cost j R) any_j t ≤ service sched_susp any_j t + (inflated_job_cost any_j - job_cost any_j) := by
  induction t with
  | zero => intro _; simp [service, service_during]
  | succ t IHt =>
    have IH := IHt (by omega')
    intro x
    rw [service_step, service_step]
    cases SCHEDn : scheduled_at (reduction.sched_new job_arrival job_cost arr_seq higher_eq_priority sched_susp inflated_job_cost j R) x t
    · have := IH x
      simp only [Bool.toNat_false, Nat.add_zero]
      omega'
    · have hs := SCHEDn
      simp only [scheduled_at, decide_eq_true_eq] at hs
      have OR := (scheduled_facts job_arrival job_cost arr_seq higher_eq_priority sched_susp j R inflated_job_cost x t hs).2.2 (by omega')
      simp only [Bool.or_eq_true] at OR
      rcases OR with LATE | SCHEDs
      · simp only [reduction.job_is_late, decide_eq_true_eq] at LATE
        simp only [Bool.toNat_true]
        omega'
      · rw [SCHEDs]
        have := IH x
        simp only [Bool.toNat_true]
        omega'

theorem sched_new_jobs_complete_later {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time) (arr_seq : arrival_sequence Job) (higher_eq_priority : JLDP_policy Job) (sched_susp : schedule Job) (j : Job) (R : time) (inflated_job_cost : Job → time) (H_job_costs_do_not_decrease : ∀ any_j, job_cost any_j ≤ inflated_job_cost any_j) (t : time) (H_before_R : t ≤ job_arrival j + R) :
    ∀ any_j, completed_by inflated_job_cost (reduction.sched_new job_arrival job_cost arr_seq higher_eq_priority sched_susp inflated_job_cost j R) any_j t = true →
      completed_by job_cost sched_susp any_j t = true := by
  intro x COMPn
  have INV := sched_new_service_invariant job_arrival job_cost arr_seq higher_eq_priority sched_susp j R inflated_job_cost t H_before_R x
  have C := H_job_costs_do_not_decrease x
  have CN := of_decide_eq_true COMPn
  exact decide_eq_true (by omega')

/-! ### Properties of the suspension predicate -/

theorem suspended_in_sched_new_implies_arrived {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time) (arr_seq : arrival_sequence Job) (higher_eq_priority : JLDP_policy Job) (sched_susp : schedule Job) (job_suspension_duration : job_suspension Job) (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched_susp) (j : Job) (R : time) (inflated_job_cost : Job → time) (any_j : Job) :
    ∀ t, reduction.suspended_in_sched_new job_arrival job_cost arr_seq higher_eq_priority sched_susp job_suspension_duration inflated_job_cost j R any_j t = true → has_arrived job_arrival any_j t = true := by
  intro t SUSP
  simp only [reduction.suspended_in_sched_new, Bool.and_eq_true] at SUSP
  exact suspended_implies_arrived job_arrival job_cost job_suspension_duration sched_susp
    H_jobs_must_arrive_to_execute any_j t SUSP.1.2

theorem suspended_in_sched_new_implies_not_completed {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time) (arr_seq : arrival_sequence Job) (higher_eq_priority : JLDP_policy Job) (sched_susp : schedule Job) (job_suspension_duration : job_suspension Job) (j : Job) (R : time) (inflated_job_cost : Job → time) (H_job_costs_do_not_decrease : ∀ any_j, job_cost any_j ≤ inflated_job_cost any_j) (any_j : Job) :
    ∀ t, reduction.suspended_in_sched_new job_arrival job_cost arr_seq higher_eq_priority sched_susp job_suspension_duration inflated_job_cost j R any_j t = true → (!completed_by inflated_job_cost (reduction.sched_new job_arrival job_cost arr_seq higher_eq_priority sched_susp inflated_job_cost j R) any_j t) = true := by
  intro t SUSP
  simp only [reduction.suspended_in_sched_new, Bool.and_eq_true, decide_eq_true_eq] at SUSP
  have NC := suspended_implies_not_completed job_arrival job_cost job_suspension_duration sched_susp any_j t SUSP.1.2
  cases COMPn : completed_by inflated_job_cost (reduction.sched_new job_arrival job_cost arr_seq higher_eq_priority sched_susp inflated_job_cost j R) any_j t
  · rfl
  · have := sched_new_jobs_complete_later job_arrival job_cost arr_seq higher_eq_priority sched_susp j R inflated_job_cost H_job_costs_do_not_decrease t (by omega') any_j COMPn
    rw [this] at NC; exact absurd NC (by simp)

theorem executes_before_suspension_in_sched_new {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time) (arr_seq : arrival_sequence Job) (higher_eq_priority : JLDP_policy Job) (sched_susp : schedule Job) (job_suspension_duration : job_suspension Job)
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched_susp) (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched_susp)
    (H_respects_self_suspensions : respects_self_suspensions job_arrival job_cost job_suspension_duration sched_susp) (j : Job) (R : time) (inflated_job_cost : Job → time) (any_j : Job) :
    ∀ t, t < job_arrival j + R → has_arrived job_arrival any_j t = true →
      (!reduction.suspended_in_sched_new job_arrival job_cost arr_seq higher_eq_priority sched_susp job_suspension_duration inflated_job_cost j R any_j t) = true → reduction.suspended_in_sched_new job_arrival job_cost arr_seq higher_eq_priority sched_susp job_suspension_duration inflated_job_cost j R any_j (t + 1) = true → scheduled_at (reduction.sched_new job_arrival job_cost arr_seq higher_eq_priority sched_susp inflated_job_cost j R) any_j t = true := by
  intro t LTr ARR NOTSUSPn SUSPn'
  have SUSPn'' := SUSPn'
  simp only [reduction.suspended_in_sched_new, Bool.and_eq_true, Bool.not_eq_true'] at SUSPn''
  obtain ⟨⟨_, SUSPs'⟩, NOTLATE'⟩ := SUSPn''
  simp only [reduction.job_is_late, decide_eq_false_iff_not, Nat.not_lt] at NOTLATE'
  by_contra NOTSCHEDn
  have NS : scheduled_at (reduction.sched_new job_arrival job_cost arr_seq higher_eq_priority sched_susp inflated_job_cost j R) any_j t = false := by simpa using NOTSCHEDn
  have SAME : service (reduction.sched_new job_arrival job_cost arr_seq higher_eq_priority sched_susp inflated_job_cost j R) any_j (t + 1) = service (reduction.sched_new job_arrival job_cost arr_seq higher_eq_priority sched_susp inflated_job_cost j R) any_j t := by
    rw [service_step, NS]; rfl
  rw [SAME] at NOTLATE'
  simp only [reduction.suspended_in_sched_new, decide_eq_true LTr, Bool.true_and, Bool.not_and,
    Bool.not_not, Bool.or_eq_true, Bool.not_eq_true'] at NOTSUSPn
  rcases NOTSUSPn with NOTSUSPs | LATE
  · have INV := sched_new_service_invariant job_arrival job_cost arr_seq higher_eq_priority sched_susp j R inflated_job_cost t (by omega') any_j
    have NSs : scheduled_at sched_susp any_j t = false := by
      cases hs : scheduled_at sched_susp any_j t
      · rfl
      · have := service_step sched_susp any_j t
        rw [hs] at this
        simp only [Bool.toNat_true] at this
        omega'
    have := executes_before_suspension job_arrival job_cost job_suspension_duration sched_susp
      H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_respects_self_suspensions any_j t ARR
      (by simp [NOTSUSPs]) SUSPs'
    rw [NSs] at this; exact Bool.noConfusion this
  · simp only [reduction.job_is_late, decide_eq_true_eq] at LATE
    have := service_mono sched_susp any_j t (t + 1) (Nat.le_succ t)
    omega'

theorem suspended_in_sched_new_no_service_since_execution {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time) (arr_seq : arrival_sequence Job) (higher_eq_priority : JLDP_policy Job) (sched_susp : schedule Job) (job_suspension_duration : job_suspension Job)
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched_susp) (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched_susp)
    (H_respects_self_suspensions : respects_self_suspensions job_arrival job_cost job_suspension_duration sched_susp) (j : Job) (R : time) (inflated_job_cost : Job → time) (any_j : Job) :
    ∀ t t_mid, reduction.suspended_in_sched_new job_arrival job_cost arr_seq higher_eq_priority sched_susp job_suspension_duration inflated_job_cost j R any_j t = true →
      (decide (time_after_last_execution job_arrival (reduction.sched_new job_arrival job_cost arr_seq higher_eq_priority sched_susp inflated_job_cost j R) any_j t ≤ t_mid) && decide (t_mid < t)) = true →
      service (reduction.sched_new job_arrival job_cost arr_seq higher_eq_priority sched_susp inflated_job_cost j R) any_j t ≤ service (reduction.sched_new job_arrival job_cost arr_seq higher_eq_priority sched_susp inflated_job_cost j R) any_j t_mid := by
  intro t t_mid SUSPn RANGE
  simp only [Bool.and_eq_true, decide_eq_true_eq] at RANGE
  have FLAT := service_flat (reduction.sched_new job_arrival job_cost arr_seq higher_eq_priority sched_susp inflated_job_cost j R) any_j t_mid t (by omega') (fun s h1 h2 => by
    cases hs : scheduled_at (reduction.sched_new job_arrival job_cost arr_seq higher_eq_priority sched_susp inflated_job_cost j R) any_j s
    · rfl
    · have := lt_tale job_arrival (reduction.sched_new job_arrival job_cost arr_seq higher_eq_priority sched_susp inflated_job_cost j R) any_j t s h2 hs
      omega')
  omega'

theorem suspended_in_sched_new_suspension_starts_no_earlier {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time) (arr_seq : arrival_sequence Job) (higher_eq_priority : JLDP_policy Job) (sched_susp : schedule Job) (job_suspension_duration : job_suspension Job)
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched_susp) (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched_susp)
    (H_respects_self_suspensions : respects_self_suspensions job_arrival job_cost job_suspension_duration sched_susp) (j : Job) (R : time) (inflated_job_cost : Job → time) (any_j : Job) :
    ∀ t, has_arrived job_arrival any_j t = true → reduction.suspended_in_sched_new job_arrival job_cost arr_seq higher_eq_priority sched_susp job_suspension_duration inflated_job_cost j R any_j t = true →
      time_after_last_execution job_arrival sched_susp any_j t ≤ time_after_last_execution job_arrival (reduction.sched_new job_arrival job_cost arr_seq higher_eq_priority sched_susp inflated_job_cost j R) any_j t := by
  have MUSTn := sched_new_jobs_must_arrive_to_execute job_arrival job_cost arr_seq higher_eq_priority sched_susp j R inflated_job_cost
  intro t
  induction t with
  | zero =>
    intro ARR _
    rw [show (Nat.zero : Nat) = 0 from rfl] at ARR ⊢
    rw [tale_none job_arrival sched_susp any_j 0 (fun s hs => absurd hs (Nat.not_lt_zero s))]
    have := last_execution_after_arrival job_arrival (reduction.sched_new job_arrival job_cost arr_seq higher_eq_priority sched_susp inflated_job_cost j R) MUSTn any_j 0
    simp only [has_arrived, decide_eq_true_eq] at this
    exact this
  | succ t IHt =>
    intro ARR SUSPn'
    rw [Nat.succ_eq_add_one] at ARR SUSPn' ⊢
    have SUSPn'' := SUSPn'
    simp only [reduction.suspended_in_sched_new, Bool.and_eq_true, decide_eq_true_eq] at SUSPn''
    obtain ⟨⟨LTr, SUSPs'⟩, _⟩ := SUSPn''
    have ARRn := last_execution_after_arrival job_arrival (reduction.sched_new job_arrival job_cost arr_seq higher_eq_priority sched_susp inflated_job_cost j R) MUSTn any_j (t + 1)
    simp only [has_arrived, decide_eq_true_eq] at ARR ARRn
    rcases Nat.lt_or_eq_of_le ARR with ARR' | EQ
    · have ARRt : has_arrived job_arrival any_j t = true := by
        simp only [has_arrived, decide_eq_true_eq]; omega'
      cases SUSPn : reduction.suspended_in_sched_new job_arrival job_cost arr_seq higher_eq_priority sched_susp job_suspension_duration inflated_job_cost j R any_j t
      · have SCHEDn := executes_before_suspension_in_sched_new job_arrival job_cost arr_seq higher_eq_priority sched_susp job_suspension_duration H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_respects_self_suspensions j R inflated_job_cost any_j t (by omega') ARRt
          (by simp [SUSPn]) SUSPn'
        have := lt_tale job_arrival (reduction.sched_new job_arrival job_cost arr_seq higher_eq_priority sched_susp inflated_job_cost j R) any_j (t + 1) t (Nat.lt_succ_self t) SCHEDn
        have LEs : time_after_last_execution job_arrival sched_susp any_j (t + 1) ≤ t + 1 := by
          have h := SUSPs'
          simp only [suspended_at, Bool.and_eq_true, decide_eq_true_eq] at h
          omega'
        omega'
      · have IH := IHt ARRt SUSPn
        have SUSPt := SUSPn
        simp only [reduction.suspended_in_sched_new, Bool.and_eq_true] at SUSPt
        have NSs : scheduled_at sched_susp any_j t = false := by
          cases hs : scheduled_at sched_susp any_j t
          · rfl
          · exact absurd SUSPt.1.2 (H_respects_self_suspensions any_j t hs)
        have Es : time_after_last_execution job_arrival sched_susp any_j (t + 1) = time_after_last_execution job_arrival sched_susp any_j t :=
          same_service_implies_same_last_execution job_arrival sched_susp any_j (t + 1) t
            (by rw [service_step, NSs]; rfl)
        have MONO := last_execution_monotonic job_arrival (reduction.sched_new job_arrival job_cost arr_seq higher_eq_priority sched_susp inflated_job_cost j R) MUSTn any_j t (t + 1) (Nat.le_succ t)
        omega'
    · have NS : ∀ s, s < t + 1 → scheduled_at sched_susp any_j s = false := by
        intro s hs
        cases h : scheduled_at sched_susp any_j s
        · rfl
        · have := H_jobs_must_arrive_to_execute any_j s h
          simp only [has_arrived, decide_eq_true_eq] at this
          omega'
      rw [tale_none job_arrival sched_susp any_j (t + 1) NS]
      exact ARRn

theorem suspended_in_sched_new_is_continuous {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time) (arr_seq : arrival_sequence Job) (higher_eq_priority : JLDP_policy Job) (sched_susp : schedule Job) (job_suspension_duration : job_suspension Job)
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched_susp) (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched_susp)
    (H_respects_self_suspensions : respects_self_suspensions job_arrival job_cost job_suspension_duration sched_susp) (j : Job) (R : time) (inflated_job_cost : Job → time) (any_j : Job) :
    ∀ t t_mid, reduction.suspended_in_sched_new job_arrival job_cost arr_seq higher_eq_priority sched_susp job_suspension_duration inflated_job_cost j R any_j t = true →
      (decide (time_after_last_execution job_arrival (reduction.sched_new job_arrival job_cost arr_seq higher_eq_priority sched_susp inflated_job_cost j R) any_j t ≤ t_mid) && decide (t_mid < t)) = true →
      reduction.suspended_in_sched_new job_arrival job_cost arr_seq higher_eq_priority sched_susp job_suspension_duration inflated_job_cost j R any_j t_mid = true := by
  intro t t_mid SUSPn RANGE
  have NOSERV := suspended_in_sched_new_no_service_since_execution job_arrival job_cost arr_seq higher_eq_priority sched_susp job_suspension_duration H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_respects_self_suspensions j R inflated_job_cost any_j t t_mid SUSPn RANGE
  have SUSPt := SUSPn
  simp only [reduction.suspended_in_sched_new, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at SUSPt
  obtain ⟨⟨LTr, SUSPs⟩, NOTLATE⟩ := SUSPt
  simp only [reduction.job_is_late, decide_eq_false_iff_not, Nat.not_lt] at NOTLATE
  simp only [Bool.and_eq_true, decide_eq_true_eq] at RANGE
  have ARR := suspended_implies_arrived job_arrival job_cost job_suspension_duration sched_susp
    H_jobs_must_arrive_to_execute any_j t SUSPs
  have NOEARLIER := suspended_in_sched_new_suspension_starts_no_earlier job_arrival job_cost arr_seq higher_eq_priority sched_susp job_suspension_duration H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_respects_self_suspensions j R inflated_job_cost any_j t ARR SUSPn
  have INV := sched_new_service_invariant job_arrival job_cost arr_seq higher_eq_priority sched_susp j R inflated_job_cost t (by omega') any_j
  have MONOs := service_mono sched_susp any_j t_mid t (by omega')
  have NCs := suspended_implies_not_completed job_arrival job_cost job_suspension_duration sched_susp any_j t SUSPs
  simp only [reduction.suspended_in_sched_new, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq]
  refine ⟨⟨by omega', ?_⟩, ?_⟩
  · apply suspended_in_suspension_interval job_arrival job_cost job_suspension_duration sched_susp
      H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_respects_self_suspensions any_j t t_mid
    · cases COMPm : completed_by job_cost sched_susp any_j t_mid
      · rfl
      · have := completion_monotonic job_cost sched_susp any_j t_mid t (by omega') COMPm
        rw [this] at NCs; exact absurd NCs (by simp)
    · have h := SUSPs
      simp only [suspended_at, Bool.and_eq_true, decide_eq_true_eq] at h
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨by omega', by omega'⟩
  · simp only [reduction.job_is_late, decide_eq_false_iff_not, Nat.not_lt]
    omega'

/-! ### Properties of the suspension table -/

theorem suspended_in_sched_new_only_inside_window {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time) (arr_seq : arrival_sequence Job) (higher_eq_priority : JLDP_policy Job) (sched_susp : schedule Job) (job_suspension_duration : job_suspension Job) (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched_susp) (j : Job) (R : time) (inflated_job_cost : Job → time) :
    ∀ any_j t, job_arrival j + R ≤ t → (!suspended_at job_arrival inflated_job_cost (reduction.reduced_suspension_duration job_arrival job_cost arr_seq higher_eq_priority sched_susp job_suspension_duration inflated_job_cost j R) (reduction.sched_new job_arrival job_cost arr_seq higher_eq_priority sched_susp inflated_job_cost j R) any_j t) = true := by
  intro x t LE
  have MUSTn := sched_new_jobs_must_arrive_to_execute job_arrival job_cost arr_seq higher_eq_priority sched_susp j R inflated_job_cost
  cases ARR : has_arrived job_arrival x t
  · cases SUSP : suspended_at job_arrival inflated_job_cost (reduction.reduced_suspension_duration job_arrival job_cost arr_seq higher_eq_priority sched_susp job_suspension_duration inflated_job_cost j R) (reduction.sched_new job_arrival job_cost arr_seq higher_eq_priority sched_susp inflated_job_cost j R) x t
    · rfl
    · have := suspended_implies_arrived job_arrival inflated_job_cost (reduction.reduced_suspension_duration job_arrival job_cost arr_seq higher_eq_priority sched_susp job_suspension_duration inflated_job_cost j R) (reduction.sched_new job_arrival job_cost arr_seq higher_eq_priority sched_susp inflated_job_cost j R) MUSTn x t SUSP
      rw [ARR] at this; exact absurd this (by simp)
  · exact suspension_duration_no_suspension_after_t_max job_arrival inflated_job_cost (reduction.sched_new job_arrival job_cost arr_seq higher_eq_priority sched_susp inflated_job_cost j R) MUSTn
      (job_arrival j + R) (reduction.suspended_in_sched_new job_arrival job_cost arr_seq higher_eq_priority sched_susp job_suspension_duration inflated_job_cost j R)
      (fun y s _ SUSP => suspended_in_sched_new_implies_arrived job_arrival job_cost arr_seq higher_eq_priority
        sched_susp job_suspension_duration H_jobs_must_arrive_to_execute j R inflated_job_cost y s SUSP) x t ARR LE

theorem sched_new_suspension_matches {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time) (arr_seq : arrival_sequence Job) (higher_eq_priority : JLDP_policy Job) (sched_susp : schedule Job) (job_suspension_duration : job_suspension Job)
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched_susp) (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched_susp)
    (H_respects_self_suspensions : respects_self_suspensions job_arrival job_cost job_suspension_duration sched_susp) (j : Job) (R : time) (inflated_job_cost : Job → time)
    (H_job_costs_do_not_decrease : ∀ any_j, job_cost any_j ≤ inflated_job_cost any_j) :
    ∀ any_j t, t < job_arrival j + R → reduction.suspended_in_sched_new job_arrival job_cost arr_seq higher_eq_priority sched_susp job_suspension_duration inflated_job_cost j R any_j t = suspended_at job_arrival inflated_job_cost (reduction.reduced_suspension_duration job_arrival job_cost arr_seq higher_eq_priority sched_susp job_suspension_duration inflated_job_cost j R) (reduction.sched_new job_arrival job_cost arr_seq higher_eq_priority sched_susp inflated_job_cost j R) any_j t := by
  have MUSTn := sched_new_jobs_must_arrive_to_execute job_arrival job_cost arr_seq higher_eq_priority sched_susp j R inflated_job_cost
  exact suspension_duration_matches_predicate_up_to_t_max job_arrival inflated_job_cost (reduction.sched_new job_arrival job_cost arr_seq higher_eq_priority sched_susp inflated_job_cost j R) MUSTn
    (job_arrival j + R) (reduction.suspended_in_sched_new job_arrival job_cost arr_seq higher_eq_priority sched_susp job_suspension_duration inflated_job_cost j R)
    (fun y s _ SUSP => suspended_in_sched_new_implies_arrived job_arrival job_cost arr_seq higher_eq_priority
      sched_susp job_suspension_duration H_jobs_must_arrive_to_execute j R inflated_job_cost y s SUSP)
    (fun y s _ SUSP => suspended_in_sched_new_implies_not_completed job_arrival job_cost arr_seq higher_eq_priority
      sched_susp job_suspension_duration j R inflated_job_cost H_job_costs_do_not_decrease y s SUSP)
    (fun y s s' _ SUSP RANGE => suspended_in_sched_new_is_continuous job_arrival job_cost arr_seq higher_eq_priority sched_susp job_suspension_duration H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_respects_self_suspensions j R inflated_job_cost y s s' SUSP RANGE)

/-- LEAN_HELPER: the new suspension predicate is no larger than the original one. -/
private theorem susp_new_le_susp {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time) (arr_seq : arrival_sequence Job) (higher_eq_priority : JLDP_policy Job) (sched_susp : schedule Job) (job_suspension_duration : job_suspension Job)
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched_susp) (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched_susp)
    (H_respects_self_suspensions : respects_self_suspensions job_arrival job_cost job_suspension_duration sched_susp) (j : Job) (R : time) (inflated_job_cost : Job → time)
    (H_job_costs_do_not_decrease : ∀ any_j, job_cost any_j ≤ inflated_job_cost any_j) (x : Job) (i : Nat) :
    (suspended_at job_arrival inflated_job_cost (reduction.reduced_suspension_duration job_arrival job_cost arr_seq higher_eq_priority sched_susp job_suspension_duration inflated_job_cost j R) (reduction.sched_new job_arrival job_cost arr_seq higher_eq_priority sched_susp inflated_job_cost j R) x i).toNat ≤ (suspended_at job_arrival job_cost job_suspension_duration sched_susp x i).toNat := by
  rcases Nat.lt_or_ge i (job_arrival j + R) with LTr | GEr
  · rw [← sched_new_suspension_matches job_arrival job_cost arr_seq higher_eq_priority sched_susp job_suspension_duration H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_respects_self_suspensions j R inflated_job_cost H_job_costs_do_not_decrease x i LTr]
    simp only [reduction.suspended_in_sched_new]
    cases suspended_at job_arrival job_cost job_suspension_duration sched_susp x i
    · simp
    · exact Bool.toNat_le _
  · have := suspended_in_sched_new_only_inside_window job_arrival job_cost arr_seq higher_eq_priority sched_susp
      job_suspension_duration H_jobs_must_arrive_to_execute j R inflated_job_cost x i GEr
    simp only [Bool.not_eq_true'] at this
    simp [this]

theorem sched_new_has_shorter_suspension {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time) (arr_seq : arrival_sequence Job) (higher_eq_priority : JLDP_policy Job) (sched_susp : schedule Job) (job_suspension_duration : job_suspension Job)
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched_susp) (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched_susp)
    (H_respects_self_suspensions : respects_self_suspensions job_arrival job_cost job_suspension_duration sched_susp) (j : Job) (R : time) (inflated_job_cost : Job → time)
    (H_job_costs_do_not_decrease : ∀ any_j, job_cost any_j ≤ inflated_job_cost any_j) :
    ∀ any_j t,
      cumulative_suspension job_arrival inflated_job_cost (reduction.reduced_suspension_duration job_arrival job_cost arr_seq higher_eq_priority sched_susp job_suspension_duration inflated_job_cost j R) (reduction.sched_new job_arrival job_cost arr_seq higher_eq_priority sched_susp inflated_job_cost j R) any_j t ≤
        cumulative_suspension job_arrival job_cost job_suspension_duration sched_susp any_j t := by
  intro x t
  unfold cumulative_suspension cumulative_suspension_during
  exact Finset.sum_le_sum (fun i _ => susp_new_le_susp job_arrival job_cost arr_seq higher_eq_priority sched_susp job_suspension_duration H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_respects_self_suspensions j R inflated_job_cost H_job_costs_do_not_decrease x i)

theorem sched_new_has_shorter_total_suspension {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time) (arr_seq : arrival_sequence Job) (higher_eq_priority : JLDP_policy Job) (sched_susp : schedule Job) (job_suspension_duration : job_suspension Job)
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched_susp) (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched_susp)
    (H_respects_self_suspensions : respects_self_suspensions job_arrival job_cost job_suspension_duration sched_susp) (j : Job) (R : time) (inflated_job_cost : Job → time)
    (H_job_costs_do_not_decrease : ∀ any_j, job_cost any_j ≤ inflated_job_cost any_j) :
    ∀ any_j,
      total_suspension inflated_job_cost (reduction.reduced_suspension_duration job_arrival job_cost arr_seq higher_eq_priority sched_susp job_suspension_duration inflated_job_cost j R) any_j ≤ total_suspension job_cost job_suspension_duration any_j := by
  intro x
  set T := job_arrival j + R with HT
  have STEP1 : total_suspension inflated_job_cost (reduction.reduced_suspension_duration job_arrival job_cost arr_seq higher_eq_priority sched_susp job_suspension_duration inflated_job_cost j R) x ≤ ∑ t ∈ Finset.Ico 0 T, (reduction.suspended_in_sched_new job_arrival job_cost arr_seq higher_eq_priority sched_susp job_suspension_duration inflated_job_cost j R x t).toNat := by
    unfold total_suspension reduction.reduced_suspension_duration build_suspension_duration
    simp only [Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_le_sum
    intro t _
    rw [Finset.sum_ite_eq]
    split <;> simp
  have STEP2 : ∑ t ∈ Finset.Ico 0 T, (reduction.suspended_in_sched_new job_arrival job_cost arr_seq higher_eq_priority sched_susp job_suspension_duration inflated_job_cost j R x t).toNat =
      cumulative_suspension job_arrival inflated_job_cost (reduction.reduced_suspension_duration job_arrival job_cost arr_seq higher_eq_priority sched_susp job_suspension_duration inflated_job_cost j R) (reduction.sched_new job_arrival job_cost arr_seq higher_eq_priority sched_susp inflated_job_cost j R) x T := by
    unfold cumulative_suspension cumulative_suspension_during
    apply Finset.sum_congr rfl
    intro t ht
    rw [Finset.mem_Ico] at ht
    rw [sched_new_suspension_matches job_arrival job_cost arr_seq higher_eq_priority sched_susp job_suspension_duration H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_respects_self_suspensions j R inflated_job_cost H_job_costs_do_not_decrease x t ht.2]
  have STEP3 := sched_new_has_shorter_suspension job_arrival job_cost arr_seq higher_eq_priority sched_susp job_suspension_duration H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_respects_self_suspensions j R inflated_job_cost H_job_costs_do_not_decrease x T
  have STEP4 := cumulative_suspension_le_total_suspension job_arrival job_cost job_suspension_duration sched_susp
    H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_respects_self_suspensions x 0 T
  unfold cumulative_suspension at STEP2 STEP3
  omega'

/-! ### Suspension-related schedule properties -/

theorem sched_new_respects_self_suspensions {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time) (arr_seq : arrival_sequence Job) (higher_eq_priority : JLDP_policy Job) (sched_susp : schedule Job) (job_suspension_duration : job_suspension Job)
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched_susp) (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched_susp)
    (H_respects_self_suspensions : respects_self_suspensions job_arrival job_cost job_suspension_duration sched_susp) (j : Job) (R : time) (inflated_job_cost : Job → time)
    (H_job_costs_do_not_decrease : ∀ any_j, job_cost any_j ≤ inflated_job_cost any_j) :
    respects_self_suspensions job_arrival inflated_job_cost (reduction.reduced_suspension_duration job_arrival job_cost arr_seq higher_eq_priority sched_susp job_suspension_duration inflated_job_cost j R) (reduction.sched_new job_arrival job_cost arr_seq higher_eq_priority sched_susp inflated_job_cost j R) := by
  intro x t SCHED SUSP
  rcases Nat.lt_or_ge t (job_arrival j + R) with LTr | GEr
  · rw [← sched_new_suspension_matches job_arrival job_cost arr_seq higher_eq_priority sched_susp job_suspension_duration H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_respects_self_suspensions j R inflated_job_cost H_job_costs_do_not_decrease x t LTr] at SUSP
    simp only [scheduled_at, decide_eq_true_eq] at SCHED
    have OR := (scheduled_facts job_arrival job_cost arr_seq higher_eq_priority sched_susp j R inflated_job_cost x t SCHED).2.2 LTr
    simp only [reduction.suspended_in_sched_new, Bool.and_eq_true, Bool.not_eq_true'] at SUSP
    simp only [Bool.or_eq_true] at OR
    rcases OR with LATE | SCHEDs
    · rw [LATE] at SUSP; exact Bool.noConfusion SUSP.2
    · exact H_respects_self_suspensions x t SCHEDs SUSP.1.2
  · have := suspended_in_sched_new_only_inside_window job_arrival job_cost arr_seq higher_eq_priority sched_susp
      job_suspension_duration H_jobs_must_arrive_to_execute j R inflated_job_cost x t GEr
    rw [SUSP] at this; exact Bool.noConfusion this

/-- LEAN_HELPER: membership in the list of late or originally scheduled jobs. -/
private theorem in_late_list {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time) (arr_seq : arrival_sequence Job) (higher_eq_priority : JLDP_policy Job) (sched_susp : schedule Job) (j : Job) (R : time) (inflated_job_cost : Job → time) (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq) (x : Job) (t : time) (ARRx : arrives_in arr_seq x)
    (PEND : pending job_arrival inflated_job_cost (reduction.sched_new job_arrival job_cost arr_seq higher_eq_priority sched_susp inflated_job_cost j R) x t = true)
    (OR : (reduction.job_is_late job_cost sched_susp inflated_job_cost (reduction.sched_new job_arrival job_cost arr_seq higher_eq_priority sched_susp inflated_job_cost j R) x t || scheduled_at sched_susp x t) = true) : x ∈ reduction.jobs_that_are_late_or_scheduled_in_sched_susp job_arrival job_cost arr_seq sched_susp inflated_job_cost (reduction.sched_new job_arrival job_cost arr_seq higher_eq_priority sched_susp inflated_job_cost j R) t := by
  unfold reduction.jobs_that_are_late_or_scheduled_in_sched_susp
  rw [List.mem_filter]
  refine ⟨?_, by simp only [PEND, OR, Bool.and_self]⟩
  have ARR := PEND
  simp only [pending, has_arrived, Bool.and_eq_true, decide_eq_true_eq] at ARR
  exact arrived_between_implies_in_arrivals job_arrival arr_seq H_arrival_times_are_consistent x 0 (t + 1) ARRx
    (by simp only [arrived_between, Bool.and_eq_true, decide_eq_true_eq]; omega')

/-- LEAN_HELPER: membership in the list of pending jobs. -/
private theorem in_pending_list {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time) (arr_seq : arrival_sequence Job) (higher_eq_priority : JLDP_policy Job) (sched_susp : schedule Job) (j : Job) (R : time) (inflated_job_cost : Job → time) (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq) (x : Job) (t : time) (ARRx : arrives_in arr_seq x)
    (PEND : pending job_arrival inflated_job_cost (reduction.sched_new job_arrival job_cost arr_seq higher_eq_priority sched_susp inflated_job_cost j R) x t = true) : x ∈ reduction.pending_jobs job_arrival arr_seq inflated_job_cost (reduction.sched_new job_arrival job_cost arr_seq higher_eq_priority sched_susp inflated_job_cost j R) t := by
  unfold reduction.pending_jobs
  rw [List.mem_filter]
  refine ⟨?_, PEND⟩
  have ARR := PEND
  simp only [pending, has_arrived, Bool.and_eq_true, decide_eq_true_eq] at ARR
  exact arrived_between_implies_in_arrivals job_arrival arr_seq H_arrival_times_are_consistent x 0 (t + 1) ARRx
    (by simp only [arrived_between, Bool.and_eq_true, decide_eq_true_eq]; omega')

/-- LEAN_HELPER: inside the window, a backlogged job of the new schedule is either in the list of late or
originally scheduled jobs, or there is such a job scheduled in the original schedule at a higher-or-equal
priority. -/
private theorem backlogged_cases {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time) (arr_seq : arrival_sequence Job) (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq) (higher_eq_priority : JLDP_policy Job) (sched_susp : schedule Job)
    (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched_susp arr_seq) (job_suspension_duration : job_suspension Job)
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched_susp) (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched_susp)
    (H_work_conserving : work_conserving job_arrival job_cost job_suspension_duration arr_seq sched_susp)
    (H_respects_self_suspensions : respects_self_suspensions job_arrival job_cost job_suspension_duration sched_susp) (j : Job) (R : time) (inflated_job_cost : Job → time)
    (H_job_costs_do_not_decrease : ∀ any_j, job_cost any_j ≤ inflated_job_cost any_j) (x : Job) (t : time) (ARRx : arrives_in arr_seq x)
    (LTr : t < job_arrival j + R)
    (PEND : pending job_arrival inflated_job_cost (reduction.sched_new job_arrival job_cost arr_seq higher_eq_priority sched_susp inflated_job_cost j R) x t = true)
    (NOTSUSP : (!suspended_at job_arrival inflated_job_cost (reduction.reduced_suspension_duration job_arrival job_cost arr_seq higher_eq_priority sched_susp job_suspension_duration inflated_job_cost j R) (reduction.sched_new job_arrival job_cost arr_seq higher_eq_priority sched_susp inflated_job_cost j R) x t) = true) :
    x ∈ reduction.jobs_that_are_late_or_scheduled_in_sched_susp job_arrival job_cost arr_seq sched_susp inflated_job_cost (reduction.sched_new job_arrival job_cost arr_seq higher_eq_priority sched_susp inflated_job_cost j R) t ∨
      (∃ j_hp, scheduled_at sched_susp j_hp t = true ∧ j_hp ∈ reduction.jobs_that_are_late_or_scheduled_in_sched_susp job_arrival job_cost arr_seq sched_susp inflated_job_cost (reduction.sched_new job_arrival job_cost arr_seq higher_eq_priority sched_susp inflated_job_cost j R) t ∧
        Prosa.Classic.Model.Schedule.Uni.Susp.Schedule.ScheduleWithSuspensions.backlogged job_arrival job_cost
          job_suspension_duration sched_susp x t = true) := by
  rw [← sched_new_suspension_matches job_arrival job_cost arr_seq higher_eq_priority sched_susp job_suspension_duration H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_respects_self_suspensions j R inflated_job_cost H_job_costs_do_not_decrease x t LTr] at NOTSUSP
  simp only [reduction.suspended_in_sched_new, decide_eq_true LTr, Bool.true_and, Bool.not_and, Bool.not_not,
    Bool.or_eq_true, Bool.not_eq_true'] at NOTSUSP
  have INV := H_job_costs_do_not_decrease x
  rcases NOTSUSP with NOTSUSPs | LATE
  · by_cases COMPs : completed_by job_cost sched_susp x t = true
    · left
      apply in_late_list job_arrival job_cost arr_seq higher_eq_priority sched_susp j R inflated_job_cost H_arrival_times_are_consistent x t ARRx PEND
      have hc := of_decide_eq_true COMPs
      have hn := PEND
      simp only [pending, completed_by, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
        Nat.not_le] at hn
      simp only [reduction.job_is_late, Bool.or_eq_true, decide_eq_true_eq]
      left; omega'
    · cases SCHEDs : scheduled_at sched_susp x t
      · right
        have BACK : Prosa.Classic.Model.Schedule.Uni.Susp.Schedule.ScheduleWithSuspensions.backlogged job_arrival
            job_cost job_suspension_duration sched_susp x t = true := by
          have hn := PEND
          simp only [pending, Bool.and_eq_true] at hn
          simp only [Prosa.Classic.Model.Schedule.Uni.Susp.Schedule.ScheduleWithSuspensions.backlogged, pending,
            hn.1, SCHEDs, NOTSUSPs, Bool.true_and, Bool.not_false, Bool.and_true]
          simpa using COMPs
        obtain ⟨j_hp, SCHEDhp⟩ := H_work_conserving x t ARRx BACK
        refine ⟨j_hp, SCHEDhp, ?_, BACK⟩
        have ARRhp := H_jobs_come_from_arrival_sequence j_hp t SCHEDhp
        apply in_late_list job_arrival job_cost arr_seq higher_eq_priority sched_susp j R inflated_job_cost H_arrival_times_are_consistent j_hp t ARRhp
        · simp only [pending, H_jobs_must_arrive_to_execute j_hp t SCHEDhp, Bool.true_and]
          cases COMPn : completed_by inflated_job_cost (reduction.sched_new job_arrival job_cost arr_seq higher_eq_priority sched_susp inflated_job_cost j R) j_hp t
          · rfl
          · have Cs := sched_new_jobs_complete_later job_arrival job_cost arr_seq higher_eq_priority sched_susp j R inflated_job_cost H_job_costs_do_not_decrease t (by omega') j_hp COMPn
            have := completed_implies_not_scheduled job_cost sched_susp j_hp H_completed_jobs_dont_execute t Cs
            rw [SCHEDhp] at this; exact absurd this (by simp)
        · simp [SCHEDhp]
      · left
        exact in_late_list job_arrival job_cost arr_seq higher_eq_priority sched_susp j R inflated_job_cost H_arrival_times_are_consistent x t ARRx PEND (by simp [SCHEDs])
  · left
    exact in_late_list job_arrival job_cost arr_seq higher_eq_priority sched_susp j R inflated_job_cost H_arrival_times_are_consistent x t ARRx PEND (by simp [LATE])

theorem sched_new_work_conserving {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time) (arr_seq : arrival_sequence Job) (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq) (higher_eq_priority : JLDP_policy Job) (sched_susp : schedule Job)
    (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched_susp arr_seq) (job_suspension_duration : job_suspension Job)
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched_susp) (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched_susp)
    (H_work_conserving : work_conserving job_arrival job_cost job_suspension_duration arr_seq sched_susp)
    (H_respects_self_suspensions : respects_self_suspensions job_arrival job_cost job_suspension_duration sched_susp) (j : Job) (R : time) (inflated_job_cost : Job → time)
    (H_job_costs_do_not_decrease : ∀ any_j, job_cost any_j ≤ inflated_job_cost any_j) :
    work_conserving job_arrival inflated_job_cost (reduction.reduced_suspension_duration job_arrival job_cost arr_seq higher_eq_priority sched_susp job_suspension_duration inflated_job_cost j R) arr_seq (reduction.sched_new job_arrival job_cost arr_seq higher_eq_priority sched_susp inflated_job_cost j R) := by
  intro x t ARRx BACK
  simp only [Prosa.Classic.Model.Schedule.Uni.Susp.Schedule.ScheduleWithSuspensions.backlogged,
    Bool.and_eq_true] at BACK
  obtain ⟨⟨PEND, _⟩, NOTSUSP⟩ := BACK
  simp only [scheduled_at, decide_eq_true_eq]
  rw [sched_new_uses_construction_function job_arrival job_cost arr_seq higher_eq_priority sched_susp j R inflated_job_cost]
  unfold reduction.build_schedule
  split
  · next LTr =>
    have IN : ∃ y, y ∈ reduction.jobs_that_are_late_or_scheduled_in_sched_susp job_arrival job_cost arr_seq sched_susp inflated_job_cost (reduction.sched_new job_arrival job_cost arr_seq higher_eq_priority sched_susp inflated_job_cost j R) t := by
      rcases backlogged_cases job_arrival job_cost arr_seq H_arrival_times_are_consistent higher_eq_priority
          sched_susp H_jobs_come_from_arrival_sequence job_suspension_duration H_jobs_must_arrive_to_execute
          H_completed_jobs_dont_execute H_work_conserving H_respects_self_suspensions j R inflated_job_cost
          H_job_costs_do_not_decrease x t ARRx LTr PEND NOTSUSP with h | ⟨j_hp, _, h, _⟩
      · exact ⟨x, h⟩
      · exact ⟨j_hp, h⟩
    obtain ⟨y, hy⟩ := IN
    have EX := seq_min_exists (higher_eq_priority t) _ y hy
    cases HP : reduction.highest_priority_late_job job_arrival job_cost arr_seq higher_eq_priority sched_susp inflated_job_cost (reduction.sched_new job_arrival job_cost arr_seq higher_eq_priority sched_susp inflated_job_cost j R) t with
    | none => unfold reduction.highest_priority_late_job at HP; rw [HP] at EX; simp at EX
    | some z => exact ⟨z, rfl⟩
  · have INx := in_pending_list job_arrival job_cost arr_seq higher_eq_priority sched_susp j R inflated_job_cost H_arrival_times_are_consistent x t ARRx PEND
    have EX := seq_min_exists (higher_eq_priority t) _ x INx
    cases HP : reduction.highest_priority_job job_arrival arr_seq higher_eq_priority inflated_job_cost (reduction.sched_new job_arrival job_cost arr_seq higher_eq_priority sched_susp inflated_job_cost j R) t with
    | none => unfold reduction.highest_priority_job at HP; rw [HP] at EX; simp at EX
    | some z => exact ⟨z, rfl⟩

theorem sched_new_respects_policy {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time) (arr_seq : arrival_sequence Job) (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq) (higher_eq_priority : JLDP_policy Job) (H_priority_is_transitive : JLDP_is_transitive higher_eq_priority)
    (H_priority_is_total : JLDP_is_total arr_seq higher_eq_priority) (sched_susp : schedule Job)
    (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched_susp arr_seq) (job_suspension_duration : job_suspension Job)
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched_susp) (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched_susp)
    (H_work_conserving : work_conserving job_arrival job_cost job_suspension_duration arr_seq sched_susp)
    (H_respects_priority :
      respects_JLDP_policy job_arrival job_cost job_suspension_duration arr_seq sched_susp higher_eq_priority)
    (H_respects_self_suspensions : respects_self_suspensions job_arrival job_cost job_suspension_duration sched_susp) (j : Job) (R : time) (inflated_job_cost : Job → time)
    (H_job_costs_do_not_decrease : ∀ any_j, job_cost any_j ≤ inflated_job_cost any_j) :
    respects_JLDP_policy job_arrival inflated_job_cost (reduction.reduced_suspension_duration job_arrival job_cost arr_seq higher_eq_priority sched_susp job_suspension_duration inflated_job_cost j R) arr_seq (reduction.sched_new job_arrival job_cost arr_seq higher_eq_priority sched_susp inflated_job_cost j R) higher_eq_priority := by
  intro x j2 t ARRx BACK SCHED
  simp only [Prosa.Classic.Model.Schedule.Uni.Susp.Schedule.ScheduleWithSuspensions.backlogged,
    Bool.and_eq_true] at BACK
  obtain ⟨⟨PEND, _⟩, NOTSUSP⟩ := BACK
  simp only [scheduled_at, decide_eq_true_eq] at SCHED
  rw [sched_new_uses_construction_function job_arrival job_cost arr_seq higher_eq_priority sched_susp j R inflated_job_cost] at SCHED
  unfold reduction.build_schedule at SCHED
  split at SCHED
  · next LTr =>
    have TOT : ∀ a b, a ∈ reduction.jobs_that_are_late_or_scheduled_in_sched_susp job_arrival job_cost arr_seq sched_susp inflated_job_cost (reduction.sched_new job_arrival job_cost arr_seq higher_eq_priority sched_susp inflated_job_cost j R) t → b ∈ reduction.jobs_that_are_late_or_scheduled_in_sched_susp job_arrival job_cost arr_seq sched_susp inflated_job_cost (reduction.sched_new job_arrival job_cost arr_seq higher_eq_priority sched_susp inflated_job_cost j R) t →
        (higher_eq_priority t a b || higher_eq_priority t b a) = true := by
      intro a b INa INb
      unfold reduction.jobs_that_are_late_or_scheduled_in_sched_susp at INa INb
      exact H_priority_is_total a b t (in_arrivals_implies_arrived arr_seq a 0 (t + 1) (List.mem_filter.mp INa).1)
        (in_arrivals_implies_arrived arr_seq b 0 (t + 1) (List.mem_filter.mp INb).1)
    have MIN := fun y (hy : y ∈ reduction.jobs_that_are_late_or_scheduled_in_sched_susp job_arrival job_cost arr_seq sched_susp inflated_job_cost (reduction.sched_new job_arrival job_cost arr_seq higher_eq_priority sched_susp inflated_job_cost j R) t) =>
      seq_min_computes_min (higher_eq_priority t) (H_priority_is_transitive t) _ TOT j2 y SCHED hy
    rcases backlogged_cases job_arrival job_cost arr_seq H_arrival_times_are_consistent higher_eq_priority
        sched_susp H_jobs_come_from_arrival_sequence job_suspension_duration H_jobs_must_arrive_to_execute
        H_completed_jobs_dont_execute H_work_conserving H_respects_self_suspensions j R inflated_job_cost
        H_job_costs_do_not_decrease x t ARRx LTr PEND NOTSUSP with h | ⟨j_hp, SCHEDhp, INhp, BACKs⟩
    · exact MIN x h
    · exact H_priority_is_transitive t j_hp j2 x (MIN j_hp INhp)
        (H_respects_priority x j_hp t ARRx BACKs SCHEDhp)
  · have INx := in_pending_list job_arrival job_cost arr_seq higher_eq_priority sched_susp j R inflated_job_cost H_arrival_times_are_consistent x t ARRx PEND
    apply seq_min_computes_min (higher_eq_priority t) (H_priority_is_transitive t) _ _ j2 x SCHED INx
    intro a b INa INb
    unfold reduction.pending_jobs at INa INb
    exact H_priority_is_total a b t (in_arrivals_implies_arrived arr_seq a 0 (t + 1) (List.mem_filter.mp INa).1)
      (in_arrivals_implies_arrived arr_seq b 0 (t + 1) (List.mem_filter.mp INb).1)

/-! ### Final remarks -/

theorem sched_new_is_valid {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time) (arr_seq : arrival_sequence Job) (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq) (higher_eq_priority : JLDP_policy Job) (H_priority_is_transitive : JLDP_is_transitive higher_eq_priority)
    (H_priority_is_total : JLDP_is_total arr_seq higher_eq_priority) (sched_susp : schedule Job)
    (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched_susp arr_seq) (job_suspension_duration : job_suspension Job)
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched_susp) (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched_susp)
    (H_work_conserving : work_conserving job_arrival job_cost job_suspension_duration arr_seq sched_susp)
    (H_respects_priority :
      respects_JLDP_policy job_arrival job_cost job_suspension_duration arr_seq sched_susp higher_eq_priority)
    (H_respects_self_suspensions : respects_self_suspensions job_arrival job_cost job_suspension_duration sched_susp) (j : Job) (R : time) (inflated_job_cost : Job → time)
    (H_job_costs_do_not_decrease : ∀ any_j, job_cost any_j ≤ inflated_job_cost any_j) :
    valid_suspension_aware_schedule job_arrival arr_seq higher_eq_priority (reduction.reduced_suspension_duration job_arrival job_cost arr_seq higher_eq_priority sched_susp job_suspension_duration inflated_job_cost j R) inflated_job_cost (reduction.sched_new job_arrival job_cost arr_seq higher_eq_priority sched_susp inflated_job_cost j R) :=
  ⟨sched_new_jobs_come_from_arrival_sequence job_arrival job_cost arr_seq higher_eq_priority sched_susp j R inflated_job_cost,
    sched_new_jobs_must_arrive_to_execute job_arrival job_cost arr_seq higher_eq_priority sched_susp j R inflated_job_cost,
    sched_new_completed_jobs_dont_execute job_arrival job_cost arr_seq higher_eq_priority sched_susp j R inflated_job_cost,
    sched_new_work_conserving job_arrival job_cost arr_seq H_arrival_times_are_consistent higher_eq_priority
      sched_susp H_jobs_come_from_arrival_sequence job_suspension_duration H_jobs_must_arrive_to_execute
      H_completed_jobs_dont_execute H_work_conserving H_respects_self_suspensions j R inflated_job_cost
      H_job_costs_do_not_decrease,
    sched_new_respects_policy job_arrival job_cost arr_seq H_arrival_times_are_consistent higher_eq_priority
      H_priority_is_transitive H_priority_is_total sched_susp H_jobs_come_from_arrival_sequence job_suspension_duration
      H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_work_conserving H_respects_priority
      H_respects_self_suspensions j R inflated_job_cost H_job_costs_do_not_decrease,
    sched_new_respects_self_suspensions job_arrival job_cost arr_seq higher_eq_priority sched_susp job_suspension_duration H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_respects_self_suspensions j R inflated_job_cost H_job_costs_do_not_decrease⟩

theorem sched_new_response_time_of_job_j {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time) (arr_seq : arrival_sequence Job) (higher_eq_priority : JLDP_policy Job) (sched_susp : schedule Job) (j : Job) (R : time) (inflated_job_cost : Job → time) (H_job_costs_do_not_decrease : ∀ any_j, job_cost any_j ≤ inflated_job_cost any_j) :
    is_response_time_bound_of_job job_arrival inflated_job_cost (reduction.sched_new job_arrival job_cost arr_seq higher_eq_priority sched_susp inflated_job_cost j R) j R = true →
      is_response_time_bound_of_job job_arrival job_cost sched_susp j R = true := by
  intro H
  exact sched_new_jobs_complete_later job_arrival job_cost arr_seq higher_eq_priority sched_susp j R inflated_job_cost H_job_costs_do_not_decrease (job_arrival j + R) (Nat.le_refl _) j H

end Prosa.Classic.Analysis.Uni.Susp.Sustainability.Allcosts.ReductionProperties.SustainabilityAllCostsProperties
