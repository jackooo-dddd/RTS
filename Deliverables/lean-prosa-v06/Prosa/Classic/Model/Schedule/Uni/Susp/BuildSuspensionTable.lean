-- Authoritative source:
-- ProsaBuddy classic Prosa (prosabuddy commit f692cb7479780cf6009493f373a309e13165201c)
-- source: classic/model/schedule/uni/susp/build_suspension_table.v
-- sha256: see Prosa-Shunqi/classic-prosa/comprehensive-classic/file_order.csv (rank 107)

import Prosa.Classic.Util.All
import Prosa.Classic.Model.Suspension
import Prosa.Classic.Model.Schedule.Uni.Susp.Schedule

/-!
Building a suspension table from a suspension predicate (Rocq module `SuspensionTableConstruction`).

Representation notes:
* `\sum_(a <= t < b | P t) F t` is `∑ t ∈ (Finset.Ico a b).filter (fun t => P t), F t`; a Boolean summed as a
  number is `Bool.toNat`; `x == y` in a filter is `x = y`.
* The section-local `Let`s (`start_of_latest_suspension := time_after_last_execution job_arrival sched`,
  `job_completed_by`) are unfolded; the statement-level `let susp_start := … in let S := … in` of
  `not_suspended_before_suspension_start` is kept as Lean `let`s.
* Boolean tests in proposition position are `= true`; `~~ b` is `(!b) = true`; `a <= x < b` is
  `(decide (a ≤ x) && decide (x < b)) = true`.
* Binder lists follow the Rocq contract.
-/

set_option linter.unusedVariables false

namespace Prosa.Classic.Model.Schedule.Uni.Susp.BuildSuspensionTable.SuspensionTableConstruction

open Prosa.Classic.Model.Time.Time
open Prosa.Classic.Model.Suspension.Suspension
open Prosa.Classic.Model.Arrival.Basic.ArrivalSequence.ArrivalSequence
open Prosa.Classic.Model.Schedule.Uni.Schedule.UniprocessorSchedule
open Prosa.Classic.Model.Schedule.Uni.Susp.LastExecution.LastExecution
open Prosa.Classic.Model.Schedule.Uni.Susp.SuspensionIntervals.SuspensionIntervals

universe v

local macro "omega'" : tactic =>
  `(tactic| ((try dsimp only [Prosa.Classic.Model.Time.Time.time,
    Prosa.Classic.Model.Time.Time.instant, Prosa.Classic.Model.Time.Time.duration] at *) <;>
    omega))

def build_suspension_duration {Job : Type v} [DecidableEq Job] (sched : schedule Job) (t_max : time) (job_suspended_at : Job → time → Bool)
    (j : Job) (s : time) : Nat :=
  ∑ t ∈ (Finset.Ico 0 t_max).filter (fun t => service sched j t = s), (job_suspended_at j t).toNat

/-! ### Proof-local facts -/

private theorem sum_toNat_eq_card (X : Finset Nat) (b : Nat → Bool) :
    ∑ i ∈ X, (b i).toNat = (X.filter (fun i => b i = true)).card := by
  rw [Finset.card_filter]
  apply Finset.sum_congr rfl
  intro i _
  cases b i <;> rfl

/-- LEAN_HELPER: a suspended instant with the same service as the start of the latest suspension (relative to a
suspended `t`) does not precede that start. -/
private theorem no_earlier_same_service {Job : Type v} [DecidableEq Job] (job_arrival : Job → time) (sched : schedule Job)
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched) (t_max : time)
    (job_suspended_at : Job → time → Bool) (H_arrived : ∀ j t, t < t_max → job_suspended_at j t = true → has_arrived job_arrival j t = true) (j : Job) (t : time) (i : Nat) (hi : i < t_max)
    (SUSPi : job_suspended_at j i = true) (SERV : service sched j i = service sched j (time_after_last_execution job_arrival sched j t)) :
    time_after_last_execution job_arrival sched j t ≤ i := by
  by_contra LT
  have ARRi := H_arrived j i hi SUSPi
  have LESS := less_service_before_start_of_suspension job_arrival sched j t i ARRi (by omega')
  rw [same_service_since_last_execution job_arrival sched H_jobs_must_arrive_to_execute j t] at SERV
  omega'

theorem not_suspended_before_suspension_start {Job : Type v} [DecidableEq Job] (job_arrival : Job → time) (sched : schedule Job)
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched) (t_max : time)
    (job_suspended_at : Job → time → Bool) (H_arrived : ∀ j t, t < t_max → job_suspended_at j t = true → has_arrived job_arrival j t = true) :
    ∀ (j : Job) (t : Nat), t < t_max → job_suspended_at j t = true →
      let susp_start := time_after_last_execution job_arrival sched j t
      let S := service sched j
      ∑ i ∈ (Finset.Ico 0 susp_start).filter (fun i => S i = S susp_start), (job_suspended_at j i).toNat = 0 := by
  intro j t LTmax SUSPt
  have ARRt := H_arrived j t LTmax SUSPt
  have LEt := last_execution_bounded_by_identity job_arrival sched j t ARRt
  simp only
  apply Finset.sum_eq_zero
  intro i hi
  rw [Finset.mem_filter, Finset.mem_Ico] at hi
  cases hs : job_suspended_at j i
  · rfl
  · have := no_earlier_same_service job_arrival sched H_jobs_must_arrive_to_execute t_max job_suspended_at H_arrived
      j t i (by omega') hs hi.2
    omega'

/-- LEAN_HELPER: the constructed suspension duration counts the qualifying instants, all of which lie in
`[time_after_last_execution t, t_max)`. -/
private theorem duration_le {Job : Type v} [DecidableEq Job] (job_arrival : Job → time) (sched : schedule Job)
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched) (t_max : time)
    (job_suspended_at : Job → time → Bool) (H_arrived : ∀ j t, t < t_max → job_suspended_at j t = true → has_arrived job_arrival j t = true) (j : Job) (t : time) :
    build_suspension_duration sched t_max job_suspended_at j (service sched j (time_after_last_execution job_arrival sched j t)) ≤ t_max - time_after_last_execution job_arrival sched j t := by
  unfold build_suspension_duration
  rw [sum_toNat_eq_card, Finset.filter_filter]
  calc _ ≤ (Finset.Ico (time_after_last_execution job_arrival sched j t) t_max).card := by
        apply Finset.card_le_card
        intro i hi
        rw [Finset.mem_filter, Finset.mem_Ico] at hi
        rw [Finset.mem_Ico]
        exact ⟨no_earlier_same_service job_arrival sched H_jobs_must_arrive_to_execute t_max job_suspended_at
          H_arrived j t i hi.1.2 hi.2.2 hi.2.1, hi.1.2⟩
    _ = t_max - time_after_last_execution job_arrival sched j t := Nat.card_Ico _ _

theorem suspension_duration_no_suspension_after_t_max {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time)
    (sched : schedule Job) (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
    (t_max : time) (job_suspended_at : Job → time → Bool) (H_arrived : ∀ j t, t < t_max → job_suspended_at j t = true → has_arrived job_arrival j t = true) :
    ∀ (j : Job) (t : time), has_arrived job_arrival j t = true → t_max ≤ t →
      (!suspended_at job_arrival job_cost (build_suspension_duration sched t_max job_suspended_at) sched j t) = true := by
  intro j t ARRt GEmax
  have LEt := last_execution_bounded_by_identity job_arrival sched j t ARRt
  have D := duration_le job_arrival sched H_jobs_must_arrive_to_execute t_max job_suspended_at H_arrived j t
  unfold suspended_at suspension_duration
  have : ¬ (t < time_after_last_execution job_arrival sched j t + build_suspension_duration sched t_max job_suspended_at j (service sched j (time_after_last_execution job_arrival sched j t))) := by omega'
  simp [this]

theorem suspension_duration_matches_predicate_up_to_t_max {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time)
    (sched : schedule Job) (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
    (t_max : time) (job_suspended_at : Job → time → Bool) (H_arrived : ∀ j t, t < t_max → job_suspended_at j t = true → has_arrived job_arrival j t = true)
    (H_not_completed : ∀ j t, t < t_max → job_suspended_at j t = true →
      (!completed_by job_cost sched j t) = true)
    (H_continuous_suspension : ∀ j t t_susp, t < t_max → job_suspended_at j t = true →
      (decide (time_after_last_execution job_arrival sched j t ≤ t_susp) && decide (t_susp < t)) = true → job_suspended_at j t_susp = true) :
    ∀ (j : Job) (t : Nat), t < t_max →
      job_suspended_at j t = suspended_at job_arrival job_cost (build_suspension_duration sched t_max job_suspended_at) sched j t := by
  intro j t LEmax
  -- instants with the same service as `t` have the same start of latest suspension
  have SAME_TALE : ∀ i, service sched j i = service sched j (time_after_last_execution job_arrival sched j t) → time_after_last_execution job_arrival sched j i = time_after_last_execution job_arrival sched j t := by
    intro i hi
    rw [same_service_since_last_execution job_arrival sched H_jobs_must_arrive_to_execute j t] at hi
    exact same_service_implies_same_last_execution job_arrival sched j i t hi
  cases SUSPt : job_suspended_at j t
  · -- `t` is not suspended: the constructed table does not suspend it either
    symm
    cases hs : suspended_at job_arrival job_cost (build_suspension_duration sched t_max job_suspended_at) sched j t
    · rfl
    · exfalso
      unfold suspended_at suspension_duration at hs
      simp only [Bool.and_eq_true] at hs
      obtain ⟨_, GE, LT⟩ := hs
      have GE' := of_decide_eq_true GE
      have LT' := of_decide_eq_true LT
      -- either some qualifying instant lies after `t` (then `t` is suspended by continuity) or all lie in
      -- `[time_after_last_execution t, t)`, which is too few
      by_cases EX : ∃ i, i < t_max ∧ service sched j i = service sched j (time_after_last_execution job_arrival sched j t) ∧
          job_suspended_at j i = true ∧ t < i
      · obtain ⟨i, hi, SERVi, SUSPi, GTi⟩ := EX
        have := H_continuous_suspension j i t hi SUSPi
          (by rw [SAME_TALE i SERVi]; simp only [Bool.and_eq_true]; exact ⟨decide_eq_true GE', decide_eq_true GTi⟩)
        rw [SUSPt] at this; exact Bool.noConfusion this
      · push_neg at EX
        have CNT : build_suspension_duration sched t_max job_suspended_at j (service sched j (time_after_last_execution job_arrival sched j t)) ≤ t - time_after_last_execution job_arrival sched j t := by
          unfold build_suspension_duration
          rw [sum_toNat_eq_card, Finset.filter_filter]
          calc _ ≤ (Finset.Ico (time_after_last_execution job_arrival sched j t) t).card := by
                apply Finset.card_le_card
                intro i hi
                rw [Finset.mem_filter, Finset.mem_Ico] at hi
                rw [Finset.mem_Ico]
                refine ⟨no_earlier_same_service job_arrival sched H_jobs_must_arrive_to_execute t_max job_suspended_at
                  H_arrived j t i hi.1.2 hi.2.2 hi.2.1, ?_⟩
                rcases Nat.lt_or_ge i t with h | h
                · exact h
                · rcases Nat.eq_or_lt_of_le h with E | G
                  · subst E; rw [SUSPt] at hi; exact absurd hi.2.2 Bool.false_ne_true
                  · exact absurd (EX i hi.1.2 hi.2.1 hi.2.2) (Nat.not_le.mpr G)
            _ = t - time_after_last_execution job_arrival sched j t := Nat.card_Ico _ _
        omega'
  · -- `t` is suspended: the constructed table also suspends it
    symm
    have ARRt := H_arrived j t LEmax SUSPt
    have LEt := last_execution_bounded_by_identity job_arrival sched j t ARRt
    have NC := H_not_completed j t LEmax SUSPt
    unfold suspended_at suspension_duration
    simp only [Bool.and_eq_true]
    refine ⟨NC, decide_eq_true LEt, decide_eq_true ?_⟩
    have CNT : t + 1 - time_after_last_execution job_arrival sched j t ≤ build_suspension_duration sched t_max job_suspended_at j (service sched j (time_after_last_execution job_arrival sched j t)) := by
      unfold build_suspension_duration
      rw [sum_toNat_eq_card, Finset.filter_filter]
      calc t + 1 - time_after_last_execution job_arrival sched j t = (Finset.Ico (time_after_last_execution job_arrival sched j t) (t + 1)).card := (Nat.card_Ico _ _).symm
        _ ≤ _ := by
          apply Finset.card_le_card
          intro i hi
          rw [Finset.mem_Ico] at hi
          rw [Finset.mem_filter, Finset.mem_Ico]
          refine ⟨⟨Nat.zero_le _, by omega'⟩, ?_, ?_⟩
          · -- the service is constant on `[time_after_last_execution t, t]`
            have M1 : service sched j (time_after_last_execution job_arrival sched j t) ≤ service sched j i := by
              unfold service service_during
              exact Finset.sum_le_sum_of_subset (Finset.Ico_subset_Ico (Nat.le_refl 0) hi.1)
            have M2 : service sched j i ≤ service sched j t := by
              unfold service service_during
              exact Finset.sum_le_sum_of_subset (Finset.Ico_subset_Ico (Nat.le_refl 0) (by omega'))
            have E := same_service_since_last_execution job_arrival sched H_jobs_must_arrive_to_execute j t
            omega'
          · rcases Nat.lt_or_ge i t with h | h
            · exact H_continuous_suspension j t i LEmax SUSPt
                (by simp only [Bool.and_eq_true]; exact ⟨decide_eq_true hi.1, decide_eq_true h⟩)
            · have : i = t := by omega'
              subst this; exact SUSPt
    omega'

end Prosa.Classic.Model.Schedule.Uni.Susp.BuildSuspensionTable.SuspensionTableConstruction
