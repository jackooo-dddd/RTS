-- Authoritative source:
-- ProsaBuddy classic Prosa (prosabuddy commit f692cb7479780cf6009493f373a309e13165201c)
-- source: classic/model/schedule/uni/limited/platform/priority_inversion_is_bounded.v
-- sha256: see Prosa-Shunqi/classic-prosa/comprehensive-classic/file_order.csv (rank 123)

import Prosa.Classic.Util.All
import Prosa.Classic.Model.Arrival.Basic.Job
import Prosa.Classic.Model.Arrival.Basic.TaskArrival
import Prosa.Classic.Model.Priority
import Prosa.Classic.Model.Schedule.Uni.Service
import Prosa.Classic.Model.Schedule.Uni.Schedule
import Prosa.Classic.Model.Schedule.Uni.Limited.Platform.Definitions
import Prosa.Classic.Model.Schedule.Uni.Limited.BusyInterval
import Prosa.Util.Epsilon

/-!
Priority inversion is bounded in models with bounded nonpreemptive segments (Rocq module
`PriorityInversionIsBounded`).

Representation notes:
* `\max_(x <- s | P x) F x` is the v0.6 `maxFiltered s P F`; `~~ b` is `!b` (in proposition position
  `(!b) = true`); `ε` is the v0.6 util notation for `1`; `t.+1` is `t + 1`; Boolean chains `a <= x <= b`,
  `a <= x < b` in proposition position are `(decide (…) && decide (…)) = true`; other Boolean tests are `= true`.
* `work_conserving` is `LimitedPreemptionPlatform.work_conserving` (the `Import`ed one); `busy_interval_prefix` and
  `quiet_time` are the `BusyIntervalJLFP` ones.
* The section-local `Let`s (`preemption_time`, `job_scheduled_at`, `job_completed_by`, `service`) are unfolded.
* Binder lists follow the Rocq contract.
-/

set_option linter.dupNamespace false
set_option linter.unusedVariables false

namespace Prosa.Classic.Model.Schedule.Uni.Limited.Platform.PriorityInversionIsBounded.PriorityInversionIsBounded

open Prosa.Classic.Model.Time.Time
open Prosa.Classic.Model.Arrival.Basic.ArrivalSequence.ArrivalSequence
open Prosa.Classic.Model.Arrival.Basic.Job.Job
open Prosa.Classic.Model.Priority.Priority
open Prosa.Classic.Model.Schedule.Uni.Schedule.UniprocessorSchedule
open Prosa.Classic.Model.Schedule.Uni.Limited.Platform.Definitions.LimitedPreemptionPlatform
open Prosa.Util.Sum (maxFiltered)
open Prosa.Util.Epsilon

universe u v

local macro "omega'" : tactic =>
  `(tactic| ((try dsimp only [Prosa.Classic.Model.Time.Time.time,
    Prosa.Classic.Model.Time.Time.instant, Prosa.Classic.Model.Time.Time.duration] at *) <;>
    omega))

def max_length_of_priority_inversion {Job : Type v} [DecidableEq Job] (job_max_nps : Job → time) (arr_seq : arrival_sequence Job)
    (higher_eq_priority : JLFP_policy Job) (j : Job) (t : time) : Nat :=
  maxFiltered (jobs_arrived_before arr_seq t) (fun j_lp => !higher_eq_priority j_lp j) (fun j_lp => job_max_nps j_lp - ε)

/-! ### Proof-local helpers -/

private theorem le_maxFiltered {I : Type _} (r : List I) (P : I → Bool) (F : I → Nat) (x : I) (hx : x ∈ r)
    (hp : P x = true) : F x ≤ maxFiltered r P F := by
  unfold maxFiltered
  have hmem : F x ∈ (r.filter P).map F := List.mem_map_of_mem (List.mem_filter.mpr ⟨hx, hp⟩)
  generalize (r.filter P).map F = L at hmem ⊢
  induction L with
  | nil => simp at hmem
  | cons a l ih =>
    rcases List.mem_cons.mp hmem with h | h
    · subst h; simp
    · exact le_trans (ih h) (by simp)

private theorem service_step {Job : Type v} [DecidableEq Job] (sched : schedule Job) (j : Job) (t : Nat) :
    service sched j (t + 1) = service sched j t + service_at sched j t := by
  unfold service service_during
  rw [Finset.sum_Ico_succ_top (Nat.zero_le _)]

private theorem service_at_le_one {Job : Type v} [DecidableEq Job] (sched : schedule Job) (j : Job) (t : Nat) : service_at sched j t ≤ 1 := by
  unfold service_at; cases scheduled_at sched j t <;> simp

/-! ### Lemmas -/

theorem not_quiet_implies_exists_scheduled_hp_job_at_preemption_point {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time) (arr_seq : arrival_sequence Job)
    (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq) (sched : schedule Job)
    (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched) (higher_eq_priority : JLFP_policy Job)
    (H_priority_is_reflexive : JLFP_is_reflexive higher_eq_priority)
    (H_priority_is_transitive : JLFP_is_transitive higher_eq_priority) (can_be_preempted : Job → time → Bool)
    (H_work_conserving : work_conserving job_arrival job_cost arr_seq sched)
    (H_respects_policy : respects_JLFP_policy_at_preemption_point job_arrival job_cost arr_seq sched can_be_preempted
      higher_eq_priority)
    (j : Job) (H_j_arrives : arrives_in arr_seq j) (H_job_cost_positive : job_cost_positive job_cost j = true)
    (t1 t2 : time) (H_busy_interval_prefix : Prosa.Classic.Model.Schedule.Uni.Limited.BusyInterval.BusyIntervalJLFP.busy_interval_prefix job_arrival job_cost arr_seq sched higher_eq_priority j t1 t2) :
    ∀ t : Nat, (decide (t1 ≤ t) && decide (t < t2)) = true → preemption_time sched can_be_preempted t = true →
      ∃ j_hp, arrived_between job_arrival j_hp t1 t2 = true ∧ higher_eq_priority j_hp j = true ∧
        scheduled_at sched j_hp t = true := by
  intro t RANGE PREEMPTP
  have RANGE' := RANGE
  simp only [Bool.and_eq_true, decide_eq_true_eq] at RANGE'
  have NOTIDLE := Prosa.Classic.Model.Schedule.Uni.Limited.BusyInterval.BusyIntervalJLFP.not_quiet_implies_not_idle job_arrival job_cost arr_seq H_arrival_times_are_consistent sched
    higher_eq_priority j H_j_arrives H_job_cost_positive H_work_conserving H_jobs_must_arrive_to_execute
    H_priority_is_reflexive t1 t2 H_busy_interval_prefix t RANGE
  cases SCHED : sched t with
  | none => exact absurd (by simp [is_idle, SCHED]) NOTIDLE
  | some j_hp =>
    have SCHEDhp : scheduled_at sched j_hp t = true := by simp [scheduled_at, SCHED]
    have HP : higher_eq_priority j_hp j = true := by
      obtain ⟨jhp', ARR', PEND', HP'⟩ := Prosa.Classic.Model.Schedule.Uni.Limited.BusyInterval.BusyIntervalJLFP.pending_hp_job_exists job_arrival job_cost arr_seq
        H_arrival_times_are_consistent sched higher_eq_priority j H_j_arrives H_job_cost_positive
        H_jobs_must_arrive_to_execute H_priority_is_reflexive t1 t2 H_busy_interval_prefix t RANGE
      by_cases EQ : jhp' = j_hp
      · subst EQ; exact HP'
      · have NS : scheduled_at sched jhp' t = false := by
          simp only [scheduled_at, SCHED, decide_eq_false_iff_not]
          intro h; exact EQ (Option.some.inj h).symm
        have BACK : backlogged job_arrival job_cost sched jhp' t = true := by simp [backlogged, PEND', NS]
        have := H_respects_policy jhp' j_hp t PREEMPTP ARR' BACK SCHEDhp
        exact H_priority_is_transitive jhp' j_hp j this HP'
    refine ⟨j_hp, ?_, HP, SCHEDhp⟩
    have ARRt := of_decide_eq_true (H_jobs_must_arrive_to_execute j_hp t SCHEDhp)
    simp only [arrived_between, Bool.and_eq_true]
    refine ⟨decide_eq_true ?_, decide_eq_true (by omega')⟩
    by_contra LT
    have C1 := H_busy_interval_prefix.2.1 j_hp (H_jobs_come_from_arrival_sequence j_hp t SCHEDhp) HP
      (decide_eq_true (by omega'))
    have C2 := completion_monotonic job_cost sched j_hp t1 t RANGE'.1 C1
    have NS := completed_implies_not_scheduled job_cost sched j_hp H_completed_jobs_dont_execute t C2
    rw [SCHEDhp] at NS; exact Bool.noConfusion NS

theorem scheduling_of_any_segment_starts_with_preemption_time {Task : Type u} [DecidableEq Task] (task_max_nps : Task → time) {Job : Type v} [DecidableEq Job]
    (job_arrival job_max_nps job_cost : Job → time) (job_task : Job → Task) (arr_seq : arrival_sequence Job)
    (sched : schedule Job) (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
    (can_be_preempted : Job → time → Bool)
    (H_correct_preemption_model : correct_preemption_model arr_seq sched can_be_preempted)
    (H_model_with_bounded_nonpreemptive_segments :
      model_with_bounded_nonpreemptive_segments job_cost job_task arr_seq can_be_preempted job_max_nps task_max_nps) :
    ∀ (j : Job) (t : time), scheduled_at sched j t = true →
      ∃ pt, (decide (job_arrival j ≤ pt) && decide (pt ≤ t)) = true ∧ preemption_time sched can_be_preempted pt = true ∧
        ∀ t', (decide (pt ≤ t') && decide (t' ≤ t)) = true → scheduled_at sched j t' = true := by
  classical
  intro s t SCHEDst
  have EX : ∃ m, m ≤ t ∧ ∀ t', m ≤ t' → t' ≤ t → scheduled_at sched s t' = true :=
    ⟨t, Nat.le_refl _, fun t' h1 h2 => by rw [show t' = t by omega']; exact SCHEDst⟩
  have SPEC := Nat.find_spec EX
  have MIN : ∀ m, m < Nat.find EX → ¬ (m ≤ t ∧ ∀ t', m ≤ t' → t' ≤ t → scheduled_at sched s t' = true) :=
    fun m h => Nat.find_min EX h
  generalize Nat.find EX = mpt at SPEC MIN
  obtain ⟨LE, ALL⟩ := SPEC
  have SCHmpt := ALL mpt (Nat.le_refl _) LE
  have ARR := of_decide_eq_true (H_jobs_must_arrive_to_execute s mpt SCHmpt)
  refine ⟨mpt, by simp only [Bool.and_eq_true]; exact ⟨decide_eq_true ARR, decide_eq_true LE⟩, ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos mpt with Z | POS
    · subst Z
      exact zero_is_pt job_cost job_task arr_seq sched can_be_preempted job_max_nps task_max_nps
        H_model_with_bounded_nonpreemptive_segments H_jobs_come_from_arrival_sequence
    · obtain ⟨m, rfl⟩ : ∃ m, mpt = m + 1 := ⟨mpt - 1, by omega'⟩
      have NSCHED : (!scheduled_at sched s m) = true := by
        cases hs : scheduled_at sched s m
        · rfl
        · exfalso
          apply MIN m (Nat.lt_succ_self m)
          refine ⟨by omega', fun t' h1 h2 => ?_⟩
          rcases Nat.eq_or_lt_of_le h1 with E | G
          · subst E; exact hs
          · exact ALL t' G h2
      exact first_moment_is_pt arr_seq sched can_be_preempted H_correct_preemption_model s m
        (H_jobs_come_from_arrival_sequence s t SCHEDst) NSCHED SCHmpt
  · intro t' H
    simp only [Bool.and_eq_true, decide_eq_true_eq] at H
    exact ALL t' H.1 H.2

theorem not_quiet_implies_exists_scheduled_hp_job_after_preemption_point {Task : Type u} [DecidableEq Task] (task_max_nps : Task → time) {Job : Type v} [DecidableEq Job]
    (job_arrival job_max_nps job_cost : Job → time) (job_task : Job → Task) (arr_seq : arrival_sequence Job)
    (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq) (sched : schedule Job)
    (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched) (higher_eq_priority : JLFP_policy Job)
    (H_priority_is_reflexive : JLFP_is_reflexive higher_eq_priority)
    (H_priority_is_transitive : JLFP_is_transitive higher_eq_priority) (can_be_preempted : Job → time → Bool)
    (H_correct_preemption_model : correct_preemption_model arr_seq sched can_be_preempted)
    (H_model_with_bounded_nonpreemptive_segments :
      model_with_bounded_nonpreemptive_segments job_cost job_task arr_seq can_be_preempted job_max_nps task_max_nps)
    (H_work_conserving : work_conserving job_arrival job_cost arr_seq sched)
    (H_respects_policy : respects_JLFP_policy_at_preemption_point job_arrival job_cost arr_seq sched can_be_preempted
      higher_eq_priority)
    (j : Job) (H_j_arrives : arrives_in arr_seq j) (H_job_cost_positive : job_cost_positive job_cost j = true)
    (t1 t2 : time) (H_busy_interval_prefix : Prosa.Classic.Model.Schedule.Uni.Limited.BusyInterval.BusyIntervalJLFP.busy_interval_prefix job_arrival job_cost arr_seq sched higher_eq_priority j t1 t2) :
    ∀ (tp t : time), preemption_time sched can_be_preempted tp = true → (decide (t1 ≤ tp) && decide (tp < t2)) = true →
      (decide (tp ≤ t) && decide (t < t2)) = true →
      ∃ j_hp, arrived_between job_arrival j_hp t1 (t + 1) = true ∧ higher_eq_priority j_hp j = true ∧
        scheduled_at sched j_hp t = true := by
  intro tp t PRPOINT H1 H2
  simp only [Bool.and_eq_true, decide_eq_true_eq] at H1 H2
  have NOTIDLE := Prosa.Classic.Model.Schedule.Uni.Limited.BusyInterval.BusyIntervalJLFP.not_quiet_implies_not_idle job_arrival job_cost arr_seq H_arrival_times_are_consistent sched
    higher_eq_priority j H_j_arrives H_job_cost_positive H_work_conserving H_jobs_must_arrive_to_execute
    H_priority_is_reflexive t1 t2 H_busy_interval_prefix t
    (by simp only [Bool.and_eq_true, decide_eq_true_eq]; constructor <;> omega')
  cases SCHED : sched t with
  | none => exact absurd (by simp [is_idle, SCHED]) NOTIDLE
  | some j_hp =>
    have SCHEDhp : scheduled_at sched j_hp t = true := by simp [scheduled_at, SCHED]
    have HP : higher_eq_priority j_hp j = true := by
      obtain ⟨prt, PRANGE, PR, SCH⟩ := scheduling_of_any_segment_starts_with_preemption_time task_max_nps job_arrival job_max_nps job_cost job_task arr_seq sched H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute can_be_preempted H_correct_preemption_model H_model_with_bounded_nonpreemptive_segments j_hp t SCHEDhp
      simp only [Bool.and_eq_true, decide_eq_true_eq] at PRANGE
      by_cases E : t1 ≤ prt
      · obtain ⟨j_lp, _, HEP, SCHEDjlp⟩ := not_quiet_implies_exists_scheduled_hp_job_at_preemption_point job_arrival job_cost arr_seq H_arrival_times_are_consistent sched H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute higher_eq_priority H_priority_is_reflexive H_priority_is_transitive can_be_preempted H_work_conserving H_respects_policy j H_j_arrives H_job_cost_positive t1 t2 H_busy_interval_prefix prt
          (by simp only [Bool.and_eq_true, decide_eq_true_eq]; constructor <;> omega') PR
        have SCHprt := SCH prt (by simp only [Bool.and_eq_true, decide_eq_true_eq]; constructor <;> omega')
        have EQ := only_one_job_scheduled sched j_hp j_lp prt SCHprt SCHEDjlp
        subst EQ; exact HEP
      · obtain ⟨j_h, _, HEP, SCHEDjh⟩ := not_quiet_implies_exists_scheduled_hp_job_at_preemption_point job_arrival job_cost arr_seq H_arrival_times_are_consistent sched H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute higher_eq_priority H_priority_is_reflexive H_priority_is_transitive can_be_preempted H_work_conserving H_respects_policy j H_j_arrives H_job_cost_positive t1 t2 H_busy_interval_prefix tp
          (by simp only [Bool.and_eq_true, decide_eq_true_eq]; constructor <;> omega') PRPOINT
        have SCHtp := SCH tp (by simp only [Bool.and_eq_true, decide_eq_true_eq]; constructor <;> omega')
        have EQ := only_one_job_scheduled sched j_hp j_h tp SCHtp SCHEDjh
        subst EQ; exact HEP
    refine ⟨j_hp, ?_, HP, SCHEDhp⟩
    have ARRt := of_decide_eq_true (H_jobs_must_arrive_to_execute j_hp t SCHEDhp)
    simp only [arrived_between, Bool.and_eq_true]
    refine ⟨decide_eq_true ?_, decide_eq_true (by omega')⟩
    by_contra LT
    have C1 := H_busy_interval_prefix.2.1 j_hp (H_jobs_come_from_arrival_sequence j_hp t SCHEDhp) HP
      (decide_eq_true (by omega'))
    have C2 := completion_monotonic job_cost sched j_hp t1 t (by omega') C1
    have NS := completed_implies_not_scheduled job_cost sched j_hp H_completed_jobs_dont_execute t C2
    rw [SCHEDhp] at NS; exact Bool.noConfusion NS

theorem not_quiet_implies_exists_scheduled_hp_job {Task : Type u} [DecidableEq Task] (task_max_nps : Task → time) {Job : Type v} [DecidableEq Job]
    (job_arrival job_max_nps job_cost : Job → time) (job_task : Job → Task) (arr_seq : arrival_sequence Job)
    (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq) (sched : schedule Job)
    (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched) (higher_eq_priority : JLFP_policy Job)
    (H_priority_is_reflexive : JLFP_is_reflexive higher_eq_priority)
    (H_priority_is_transitive : JLFP_is_transitive higher_eq_priority) (can_be_preempted : Job → time → Bool)
    (H_correct_preemption_model : correct_preemption_model arr_seq sched can_be_preempted)
    (H_model_with_bounded_nonpreemptive_segments :
      model_with_bounded_nonpreemptive_segments job_cost job_task arr_seq can_be_preempted job_max_nps task_max_nps)
    (H_work_conserving : work_conserving job_arrival job_cost arr_seq sched)
    (H_respects_policy : respects_JLFP_policy_at_preemption_point job_arrival job_cost arr_seq sched can_be_preempted
      higher_eq_priority)
    (j : Job) (H_j_arrives : arrives_in arr_seq j) (H_job_cost_positive : job_cost_positive job_cost j = true)
    (t1 t2 : time) (H_busy_interval_prefix : Prosa.Classic.Model.Schedule.Uni.Limited.BusyInterval.BusyIntervalJLFP.busy_interval_prefix job_arrival job_cost arr_seq sched higher_eq_priority j t1 t2) (K : time)
    (H_preemption_time_exists : ∃ pr_t, preemption_time sched can_be_preempted pr_t = true ∧ (decide (t1 ≤ pr_t) && decide (pr_t ≤ t1 + K)) = true) :
    ∀ t : Nat, (decide (t1 + K ≤ t) && decide (t < t2)) = true →
      ∃ j_hp, arrived_between job_arrival j_hp t1 (t + 1) = true ∧ higher_eq_priority j_hp j = true ∧
        scheduled_at sched j_hp t = true := by
  intro t H
  simp only [Bool.and_eq_true, decide_eq_true_eq] at H
  obtain ⟨prt, PR, R⟩ := H_preemption_time_exists
  simp only [Bool.and_eq_true, decide_eq_true_eq] at R
  exact not_quiet_implies_exists_scheduled_hp_job_after_preemption_point task_max_nps job_arrival job_max_nps job_cost job_task arr_seq H_arrival_times_are_consistent sched H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute higher_eq_priority H_priority_is_reflexive H_priority_is_transitive can_be_preempted H_correct_preemption_model H_model_with_bounded_nonpreemptive_segments H_work_conserving H_respects_policy j H_j_arrives H_job_cost_positive t1 t2 H_busy_interval_prefix prt t PR
    (by simp only [Bool.and_eq_true, decide_eq_true_eq]; constructor <;> omega')
    (by simp only [Bool.and_eq_true, decide_eq_true_eq]; constructor <;> omega')

theorem hp_job_not_scheduled_before_quiet_time {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time)
    (arr_seq : arrival_sequence Job) (sched : schedule Job)
    (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched) (higher_eq_priority : JLFP_policy Job)
    (j : Job) :
    ∀ (jhp : Job) (t : time), Prosa.Classic.Model.Schedule.Uni.Limited.BusyInterval.BusyIntervalJLFP.quiet_time job_arrival job_cost arr_seq sched higher_eq_priority j (t + 1) → scheduled_at sched jhp (t + 1) = true →
      higher_eq_priority jhp j = true → (!scheduled_at sched jhp t) = true := by
  intro jhp t QT SCHED1 HP
  cases SCHED2 : scheduled_at sched jhp t
  · rfl
  · exfalso
    have ARR := of_decide_eq_true (H_jobs_must_arrive_to_execute jhp t SCHED2)
    have C := QT jhp (H_jobs_come_from_arrival_sequence jhp t SCHED2) HP (decide_eq_true (by omega'))
    have NS := completed_implies_not_scheduled job_cost sched jhp H_completed_jobs_dont_execute (t + 1) C
    rw [SCHED1] at NS; exact Bool.noConfusion NS

theorem low_priority_job_arrives_before_busy_interval_prefix {Task : Type u} [DecidableEq Task] (task_max_nps : Task → time) {Job : Type v} [DecidableEq Job]
    (job_arrival job_max_nps job_cost : Job → time) (job_task : Job → Task) (arr_seq : arrival_sequence Job)
    (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq) (sched : schedule Job)
    (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched) (higher_eq_priority : JLFP_policy Job)
    (H_priority_is_reflexive : JLFP_is_reflexive higher_eq_priority)
    (H_priority_is_transitive : JLFP_is_transitive higher_eq_priority) (can_be_preempted : Job → time → Bool)
    (H_correct_preemption_model : correct_preemption_model arr_seq sched can_be_preempted)
    (H_model_with_bounded_nonpreemptive_segments :
      model_with_bounded_nonpreemptive_segments job_cost job_task arr_seq can_be_preempted job_max_nps task_max_nps)
    (H_work_conserving : work_conserving job_arrival job_cost arr_seq sched)
    (H_respects_policy : respects_JLFP_policy_at_preemption_point job_arrival job_cost arr_seq sched can_be_preempted
      higher_eq_priority)
    (j : Job) (H_j_arrives : arrives_in arr_seq j) (H_job_cost_positive : job_cost_positive job_cost j = true)
    (t1 t2 : time) (H_busy_interval_prefix : Prosa.Classic.Model.Schedule.Uni.Limited.BusyInterval.BusyIntervalJLFP.busy_interval_prefix job_arrival job_cost arr_seq sched higher_eq_priority j t1 t2) :
    ∀ (jlp : Job) (t : time), (decide (t1 ≤ t) && decide (t < t2)) = true → scheduled_at sched jlp t = true →
      (!higher_eq_priority jlp j) = true → job_arrival jlp < t1 := by
  intro jlp t H SCHED LP
  simp only [Bool.and_eq_true, decide_eq_true_eq] at H
  by_contra ARR
  obtain ⟨pt, PRANGE, PT, FA⟩ := scheduling_of_any_segment_starts_with_preemption_time task_max_nps job_arrival job_max_nps job_cost job_task arr_seq sched H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute can_be_preempted H_correct_preemption_model H_model_with_bounded_nonpreemptive_segments jlp t SCHED
  simp only [Bool.and_eq_true, decide_eq_true_eq] at PRANGE
  obtain ⟨jhp, _, HP, SCHEDhp⟩ := not_quiet_implies_exists_scheduled_hp_job_at_preemption_point job_arrival job_cost arr_seq H_arrival_times_are_consistent sched H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute higher_eq_priority H_priority_is_reflexive H_priority_is_transitive can_be_preempted H_work_conserving H_respects_policy j H_j_arrives H_job_cost_positive t1 t2 H_busy_interval_prefix pt
    (by simp only [Bool.and_eq_true, decide_eq_true_eq]; constructor <;> omega') PT
  have SCHpt := FA pt (by simp only [Bool.and_eq_true, decide_eq_true_eq]; constructor <;> omega')
  have EQ := only_one_job_scheduled sched jlp jhp pt SCHpt SCHEDhp
  subst EQ
  rw [HP] at LP; exact Bool.noConfusion LP

theorem low_priority_job_scheduled_before_busy_interval_prefix {Task : Type u} [DecidableEq Task] (task_max_nps : Task → time) {Job : Type v} [DecidableEq Job]
    (job_arrival job_max_nps job_cost : Job → time) (job_task : Job → Task) (arr_seq : arrival_sequence Job)
    (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq) (sched : schedule Job)
    (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched) (higher_eq_priority : JLFP_policy Job)
    (H_priority_is_reflexive : JLFP_is_reflexive higher_eq_priority)
    (H_priority_is_transitive : JLFP_is_transitive higher_eq_priority) (can_be_preempted : Job → time → Bool)
    (H_correct_preemption_model : correct_preemption_model arr_seq sched can_be_preempted)
    (H_model_with_bounded_nonpreemptive_segments :
      model_with_bounded_nonpreemptive_segments job_cost job_task arr_seq can_be_preempted job_max_nps task_max_nps)
    (H_work_conserving : work_conserving job_arrival job_cost arr_seq sched)
    (H_respects_policy : respects_JLFP_policy_at_preemption_point job_arrival job_cost arr_seq sched can_be_preempted
      higher_eq_priority)
    (j : Job) (H_j_arrives : arrives_in arr_seq j) (H_job_cost_positive : job_cost_positive job_cost j = true)
    (t1 t2 : time) (H_busy_interval_prefix : Prosa.Classic.Model.Schedule.Uni.Limited.BusyInterval.BusyIntervalJLFP.busy_interval_prefix job_arrival job_cost arr_seq sched higher_eq_priority j t1 t2) :
    ∀ (jlp : Job) (t : time), (decide (t1 ≤ t) && decide (t < t2)) = true → scheduled_at sched jlp t = true →
      (!higher_eq_priority jlp j) = true → ∃ t', t' < t1 ∧ scheduled_at sched jlp t' = true := by
  intro jlp t NEQ SCHED LP
  have ARR := low_priority_job_arrives_before_busy_interval_prefix task_max_nps job_arrival job_max_nps job_cost job_task arr_seq H_arrival_times_are_consistent sched H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute higher_eq_priority H_priority_is_reflexive H_priority_is_transitive can_be_preempted H_correct_preemption_model H_model_with_bounded_nonpreemptive_segments H_work_conserving H_respects_policy j H_j_arrives H_job_cost_positive t1 t2 H_busy_interval_prefix jlp t NEQ SCHED LP
  simp only [Bool.and_eq_true, decide_eq_true_eq] at NEQ
  obtain ⟨pt, PRANGE, PT, SCHEDc⟩ := scheduling_of_any_segment_starts_with_preemption_time task_max_nps job_arrival job_max_nps job_cost job_task arr_seq sched H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute can_be_preempted H_correct_preemption_model H_model_with_bounded_nonpreemptive_segments jlp t SCHED
  simp only [Bool.and_eq_true, decide_eq_true_eq] at PRANGE
  have LTpt : pt < t1 := by
    by_contra CONTR
    obtain ⟨jhp, _, HP, SCHEDhp⟩ := not_quiet_implies_exists_scheduled_hp_job_at_preemption_point job_arrival job_cost arr_seq H_arrival_times_are_consistent sched H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute higher_eq_priority H_priority_is_reflexive H_priority_is_transitive can_be_preempted H_work_conserving H_respects_policy j H_j_arrives H_job_cost_positive t1 t2 H_busy_interval_prefix pt
      (by simp only [Bool.and_eq_true, decide_eq_true_eq]; constructor <;> omega') PT
    have SCHpt := SCHEDc pt (by simp only [Bool.and_eq_true, decide_eq_true_eq]; constructor <;> omega')
    have EQ := only_one_job_scheduled sched jhp jlp pt SCHEDhp SCHpt
    subst EQ
    rw [HP] at LP; exact Bool.noConfusion LP
  exact ⟨t1 - 1, by omega', SCHEDc (t1 - 1) (by simp only [Bool.and_eq_true, decide_eq_true_eq]; constructor <;> omega')⟩

theorem preemption_time_exists {Task : Type u} [DecidableEq Task] (task_max_nps : Task → time) {Job : Type v} [DecidableEq Job]
    (job_arrival job_max_nps job_cost : Job → time) (job_task : Job → Task) (arr_seq : arrival_sequence Job)
    (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq) (sched : schedule Job)
    (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched) (higher_eq_priority : JLFP_policy Job)
    (H_priority_is_reflexive : JLFP_is_reflexive higher_eq_priority)
    (H_priority_is_transitive : JLFP_is_transitive higher_eq_priority) (can_be_preempted : Job → time → Bool)
    (H_correct_preemption_model : correct_preemption_model arr_seq sched can_be_preempted)
    (H_model_with_bounded_nonpreemptive_segments :
      model_with_bounded_nonpreemptive_segments job_cost job_task arr_seq can_be_preempted job_max_nps task_max_nps)
    (H_work_conserving : work_conserving job_arrival job_cost arr_seq sched)
    (H_respects_policy : respects_JLFP_policy_at_preemption_point job_arrival job_cost arr_seq sched can_be_preempted
      higher_eq_priority)
    (j : Job) (H_j_arrives : arrives_in arr_seq j) (H_job_cost_positive : job_cost_positive job_cost j = true)
    (t1 t2 : time) (H_busy_interval_prefix : Prosa.Classic.Model.Schedule.Uni.Limited.BusyInterval.BusyIntervalJLFP.busy_interval_prefix job_arrival job_cost arr_seq sched higher_eq_priority j t1 t2) :
    ∃ pr_t, preemption_time sched can_be_preempted pr_t = true ∧
      (decide (t1 ≤ pr_t) &&
        decide (pr_t ≤ t1 + max_length_of_priority_inversion job_max_nps arr_seq higher_eq_priority j t1)) = true := by
  have PREF := H_busy_interval_prefix
  obtain ⟨NEM, QT1, NQT, HPJ⟩ := PREF
  cases SCHED : sched t1 with
  | none =>
    refine ⟨t1, by simp [preemption_time, SCHED], ?_⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq]; constructor <;> omega'
  | some s =>
    have SCHs : scheduled_at sched s t1 = true := by simp [scheduled_at, SCHED]
    have ARRs := H_jobs_come_from_arrival_sequence s t1 SCHs
    cases PRIO : higher_eq_priority s j
    · -- a lower-priority job is scheduled at `t1`: it reaches a preemption point within its maximal segment
      classical
      obtain ⟨_, _, _, EXPP⟩ := H_model_with_bounded_nonpreemptive_segments s ARRs
      obtain ⟨pp, PPR, PP⟩ := EXPP (service sched s t1)
        (by simp only [Bool.and_eq_true, decide_eq_true_eq]; exact ⟨Nat.zero_le _, H_completed_jobs_dont_execute s t1⟩)
      simp only [Bool.and_eq_true, decide_eq_true_eq] at PPR
      have EX : ∃ Δ, Δ ≤ job_max_nps s - ε ∧ can_be_preempted s (service sched s t1 + Δ) = true :=
        ⟨pp - service sched s t1, by omega', by rw [show service sched s t1 + (pp - service sched s t1) = pp by omega']; exact PP⟩
      have SPEC := Nat.find_spec EX
      have MIN : ∀ m, m < Nat.find EX →
          ¬ (m ≤ job_max_nps s - ε ∧ can_be_preempted s (service sched s t1 + m) = true) :=
        fun m h => Nat.find_min EX h
      generalize Nat.find EX = Δ at SPEC MIN
      obtain ⟨LEΔ, PPΔ⟩ := SPEC
      -- `s` keeps executing in `[t1, t1 + Δ)`
      have Fact2 : ∀ δ, δ ≤ Δ → service sched s (t1 + δ) = service sched s t1 + δ ∧
          (δ < Δ → scheduled_at sched s (t1 + δ) = true) := by
        intro δ
        induction δ with
        | zero =>
          intro _
          refine ⟨by simp, fun hΔ => ?_⟩
          simpa using SCHs
        | succ δ IH =>
          intro hδ
          obtain ⟨S, SC⟩ := IH (by omega')
          have SCδ := SC (by omega')
          have SERV : service sched s (t1 + (δ + 1)) = service sched s t1 + (δ + 1) := by
            rw [show t1 + (δ + 1) = (t1 + δ) + 1 by omega', service_step, S]
            simp [service_at, SCδ]; omega'
          refine ⟨SERV, fun hlt => ?_⟩
          have NP : (!can_be_preempted s (service sched s (t1 + (δ + 1)))) = true := by
            cases hc : can_be_preempted s (service sched s (t1 + (δ + 1)))
            · rfl
            · exfalso
              apply MIN (δ + 1) hlt
              exact ⟨by omega', by rw [← SERV]; exact hc⟩
          exact (H_correct_preemption_model s ARRs).1 _ NP
      have INbefore := low_priority_job_arrives_before_busy_interval_prefix task_max_nps job_arrival job_max_nps job_cost job_task arr_seq H_arrival_times_are_consistent sched H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute higher_eq_priority H_priority_is_reflexive H_priority_is_transitive can_be_preempted H_correct_preemption_model H_model_with_bounded_nonpreemptive_segments H_work_conserving H_respects_policy j H_j_arrives H_job_cost_positive t1 t2 H_busy_interval_prefix s t1
        (by simp only [Bool.and_eq_true, decide_eq_true_eq]; exact ⟨Nat.le_refl _, NEM⟩) SCHs (by simp [PRIO])
      have INL : s ∈ jobs_arrived_before arr_seq t1 := by
        unfold jobs_arrived_before
        exact arrived_between_implies_in_arrivals job_arrival arr_seq H_arrival_times_are_consistent s 0 t1 ARRs
          (by simp only [arrived_between, Bool.and_eq_true]; exact ⟨decide_eq_true (Nat.zero_le _), decide_eq_true INbefore⟩)
      have BOUND := le_maxFiltered (jobs_arrived_before arr_seq t1) (fun j_lp => !higher_eq_priority j_lp j)
        (fun j_lp => job_max_nps j_lp - ε) s INL (by simp [PRIO])
      refine ⟨t1 + Δ, ?_, ?_⟩
      · unfold preemption_time
        cases S2 : sched (t1 + Δ) with
        | none => rfl
        | some s0 =>
          dsimp only
          by_cases EQ : s0 = s
          · subst EQ
            rw [(Fact2 Δ (Nat.le_refl _)).1]
            exact PPΔ
          · rcases Nat.eq_zero_or_pos Δ with Z | POS
            · subst Z; rw [Nat.add_zero, SCHED] at S2; exact absurd (Option.some.inj S2) (Ne.symm EQ)
            · obtain ⟨d, rfl⟩ : ∃ d, Δ = d + 1 := ⟨Δ - 1, by omega'⟩
              have SCHs0 : scheduled_at sched s0 (t1 + (d + 1)) = true := by simp [scheduled_at, S2]
              have NS0 : (!scheduled_at sched s0 (t1 + d)) = true := by
                cases h : scheduled_at sched s0 (t1 + d)
                · rfl
                · exfalso
                  have := only_one_job_scheduled sched s0 s (t1 + d) h ((Fact2 d (by omega')).2 (by omega'))
                  exact EQ this
              have := first_moment_is_pt arr_seq sched can_be_preempted H_correct_preemption_model s0 (t1 + d)
                (H_jobs_come_from_arrival_sequence s0 _ SCHs0) NS0 (by rw [Nat.add_assoc]; exact SCHs0)
              unfold preemption_time at this
              rw [Nat.add_assoc, S2] at this
              exact this
      · simp only [Bool.and_eq_true, decide_eq_true_eq]
        unfold max_length_of_priority_inversion
        constructor <;> omega'
    · -- a higher-or-equal-priority job is scheduled at `t1`: `t1` is a preemption time
      refine ⟨t1, ?_, by simp only [Bool.and_eq_true, decide_eq_true_eq]; constructor <;> omega'⟩
      rcases Nat.eq_zero_or_pos t1 with Z | POS
      · rw [Z]
        exact zero_is_pt job_cost job_task arr_seq sched can_be_preempted job_max_nps task_max_nps
          H_model_with_bounded_nonpreemptive_segments H_jobs_come_from_arrival_sequence
      · obtain ⟨m, hm⟩ : ∃ m, t1 = m + 1 := ⟨t1 - 1, by omega'⟩
        rw [hm] at QT1 SCHs ⊢
        have NS := hp_job_not_scheduled_before_quiet_time job_arrival job_cost arr_seq sched
          H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
          higher_eq_priority j s m QT1 SCHs PRIO
        exact first_moment_is_pt arr_seq sched can_be_preempted H_correct_preemption_model s m ARRs NS SCHs

end Prosa.Classic.Model.Schedule.Uni.Limited.Platform.PriorityInversionIsBounded.PriorityInversionIsBounded
