-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/facts/suspension.v

import Prosa.Model.Readiness.Suspension
import Mathlib.Algebra.BigOperators.Intervals

namespace Prosa.Analysis.Facts.Suspension

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Ready
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Behavior.Time
open Prosa.Analysis.Definitions.Progress
open Prosa.Analysis.Facts.Behavior.Service
open Prosa.Model.Readiness.Suspension
open scoped BigOperators

/-! Basic facts about self-suspending jobs.

Binders follow the elaborated source types: each statement takes the section inputs and hypotheses it uses, in
their elaborated order. The source's section-local readiness instance is the accepted named definition
`suspension_ready_instance`, passed explicitly. Representation: a Boolean in `Prop` position is `= true`; `~~ b`
is `(!b) = true`; `a <= t < b` is the decided conjunction `(decide (a ≤ t) && decide (t < b)) = true`;
`x \in xs` is `decide (x ∈ xs) = true`; `index_iota a b` is `List.range' a (b - a)`; `exists2 x, P x & Q x` is
`∃ x, P x ∧ Q x`; `x == y` on `nat` is `decide (x = y)`; the filtered interval sum
`\sum_(a <= t < b | P t) F t` is the `Finset.Ico` sum over `Nat` of `if P t then F t else 0`; `nat_of_bool` is
`Bool.toNat`. -/

section Suspensions

variable {Job : JobType} [DecidableEq Job] [JobArrival Job] [JobCost Job] [JobSuspension Job]
variable {PState : ProcessorState Job} (sched : schedule PState)

/-- A suspended job is not ready. -/
theorem suspended_implies_job_not_ready (j : Job) (t : instant) :
    suspended sched j t = true →
      (!(@job_ready Job _ PState _ _ suspension_ready_instance sched j t)) = true := by
  intro h
  unfold suspended at h
  have hparts := Bool.and_eq_true_iff.mp h
  have hnp : suspension_has_passed sched j t = false := by simpa using hparts.1
  show (!(suspension_has_passed sched j t && !completed_by sched j t)) = true
  rw [hnp]
  rfl

/-- A suspended job is not scheduled in a valid schedule. -/
theorem suspended_implies_not_scheduled (arr_seq : arrival_sequence Job) :
    @valid_schedule Job _ _ PState sched _ suspension_ready_instance arr_seq →
    ∀ (j : Job) (t : instant), suspended sched j t = true → (!scheduled_at sched j t) = true := by
  intro hvalid j t hsus
  have hnr := suspended_implies_job_not_ready sched j t hsus
  cases hsch : scheduled_at sched j t with
  | false => rfl
  | true =>
    have hready := hvalid.2 j t hsch
    rw [hready] at hnr
    exact absurd hnr (by decide)

/-- A suspended job has arrived. -/
theorem suspended_implies_arrived (j : Job) (t : instant) :
    suspended sched j t = true → has_arrived j t = true := by
  intro h
  unfold suspended at h
  have hpend := (Bool.and_eq_true_iff.mp h).2
  unfold pending at hpend
  exact (Bool.and_eq_true_iff.mp hpend).1

/-- A suspended job is pending. -/
theorem suspended_implies_pending (j : Job) (t : instant) :
    suspended sched j t = true → pending sched j t = true := by
  intro h
  unfold suspended at h
  exact (Bool.and_eq_true_iff.mp h).2

/-- A suspended job is not backlogged. -/
theorem suspended_implies_not_backlogged (j : Job) (t : instant) :
    suspended sched j t = true →
      (!(@backlogged Job _ PState _ _ suspension_ready_instance sched j t)) = true := by
  intro h
  have hnr := suspended_implies_job_not_ready sched j t h
  unfold backlogged
  cases hr : @job_ready Job _ PState _ _ suspension_ready_instance sched j t with
  | false => rfl
  | true => rw [hr] at hnr; exact absurd hnr (by decide)

/-- A pending job that is not suspended is ready. -/
theorem pending_and_not_suspended_implies_ready (j : Job) (t : instant) :
    pending sched j t = true → (!suspended sched j t) = true →
      @job_ready Job _ PState _ _ suspension_ready_instance sched j t = true := by
  intro hpend hns
  have hpassed : suspension_has_passed sched j t = true := by
    unfold suspended at hns
    rw [hpend] at hns
    cases hp : suspension_has_passed sched j t with
    | true => rfl
    | false => rw [hp] at hns; exact absurd hns (by decide)
  have hnc : (!completed_by sched j t) = true := by
    unfold pending at hpend
    exact (Bool.and_eq_true_iff.mp hpend).2
  show (suspension_has_passed sched j t && !completed_by sched j t) = true
  rw [hpassed, hnc]
  rfl

/-- LEAN_HELPER: the summand of the filtered interval sums. -/
private theorem summand_le_one (j : Job) (ρ : work) (t : Nat) :
    (if service sched j t = ρ then (suspended sched j t).toNat else 0) ≤ 1 := by
  split
  · cases suspended sched j t <;> simp
  · exact Nat.zero_le 1

/-- LEAN_HELPER: a filtered interval sum of such summands is at most the interval length. -/
private theorem filtered_sum_le_length (j : Job) (ρ : work) (a b : Nat) :
    ∑ t ∈ Finset.Ico (α := Nat) a b, (if service sched j t = ρ then (suspended sched j t).toNat else 0) ≤ b - a := by
  calc ∑ t ∈ Finset.Ico (α := Nat) a b, (if service sched j t = ρ then (suspended sched j t).toNat else 0)
      ≤ ∑ _t ∈ Finset.Ico (α := Nat) a b, 1 := Finset.sum_le_sum fun t _ => summand_le_one sched j ρ t
    _ = b - a := by simp

/-- If `j` is suspended at `tf` with service `ρ` and the interval ends within the suspension bound, the bound
holds trivially. -/
theorem suspension_bounded_trivial (j : Job) (t1 t2 : instant) (ρ : work) (tf : instant) :
    (decide (t1 ≤ tf) && decide (tf < t2)) = true → suspended sched j tf = true →
      service sched j tf = ρ → t2 - tf ≤ job_suspension j ρ →
      ∑ t ∈ Finset.Ico (α := Nat) tf t2,
          (if service sched j t = ρ then (suspended sched j t).toNat else 0) ≤ job_suspension j ρ := by
  intro _ _ _ hle
  exact Nat.le_trans (filtered_sum_le_length sched j ρ tf t2) hle

/-- LEAN_HELPER: once the suspension that started at `tf` with service `ρ` has lasted `job_suspension j ρ`
time units, the job is not suspended at any later instant where its service is still `ρ`. -/
private theorem not_suspended_after (j : Job) (ρ : work) (tf t : Nat)
    (hsus : suspended sched j tf = true) (hserv : service sched j tf = ρ)
    (hge : tf + job_suspension j ρ ≤ t) (hst : service sched j t = ρ) :
    suspended sched j t = false := by
  have harr : job_arrival j ≤ tf := by
    have := suspended_implies_arrived sched j tf hsus
    unfold has_arrived at this
    exact of_decide_eq_true this
  have hlo : ρ ≤ service sched j (t - job_suspension j ρ) := by
    have hm := service_monotonic sched j tf (t - job_suspension j ρ)
      (by (try dsimp only [instant, duration, work] at *); omega)
    rw [hserv] at hm
    exact hm
  have hhi : service sched j (t - job_suspension j ρ) ≤ ρ := by
    have hm := service_monotonic sched j (t - job_suspension j ρ) t (Nat.sub_le _ _)
    rw [hst] at hm
    exact hm
  have hpassed : suspension_has_passed sched j t = true := by
    unfold suspension_has_passed no_progress_for no_progress
    simp only [hst, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨Nat.le_trans (Nat.add_le_add_right harr _) hge, Nat.le_antisymm hhi hlo⟩
  unfold suspended
  rw [hpassed]
  rfl

/-- If `j` is suspended at `tf` with service `ρ` and the interval extends beyond the suspension bound, the bound
still holds. -/
theorem suspension_bounded_longer_interval (j : Job) (t1 t2 : instant) (ρ : work) (tf : instant) :
    (decide (t1 ≤ tf) && decide (tf < t2)) = true → suspended sched j tf = true →
      service sched j tf = ρ → job_suspension j ρ < t2 - tf →
      ∑ t ∈ Finset.Ico (α := Nat) tf t2,
          (if service sched j t = ρ then (suspended sched j t).toNat else 0) ≤ job_suspension j ρ := by
  intro _ hsus hserv hgt
  have hsplit := Finset.sum_Ico_consecutive
    (fun t => if service sched j t = ρ then (suspended sched j t).toNat else 0)
    (Nat.le_add_right tf (job_suspension j ρ)) (show tf + job_suspension j ρ ≤ t2 by (try dsimp only [instant, duration, work] at *); omega)
  rw [← hsplit]
  have hzero : ∑ t ∈ Finset.Ico (α := Nat) (tf + job_suspension j ρ) t2,
      (if service sched j t = ρ then (suspended sched j t).toNat else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro t ht
    have hge := (Finset.mem_Ico.mp ht).1
    split
    · rename_i hst
      rw [not_suspended_after sched j ρ tf t hsus hserv hge hst]
      rfl
    · rfl
  rw [hzero, Nat.add_zero]
  have := filtered_sum_le_length sched j ρ tf (tf + job_suspension j ρ)
  (try dsimp only [instant, duration, work] at *); omega

/-- If `j` is first suspended with service `ρ` at `tf` within `[t1, t2)`, the suspension bound holds on
`[t1, t2)`. -/
theorem suspension_bounded_in_interval_aux (j : Job) (t1 t2 : instant) (ρ : work) (tf : instant) :
    (decide (t1 ≤ tf) && decide (tf < t2)) = true → suspended sched j tf = true →
      service sched j tf = ρ →
      (∀ t0 : Nat, (decide (t1 ≤ t0) && decide (t0 < tf)) = true →
        (!(suspended sched j t0 && decide (service sched j t0 = ρ))) = true) →
      ∑ t ∈ Finset.Ico (α := Nat) t1 t2,
          (if service sched j t = ρ then (suspended sched j t).toNat else 0) ≤ job_suspension j ρ := by
  intro hin hsus hserv hbefore
  have hin' := Bool.and_eq_true_iff.mp hin
  have h1 : t1 ≤ tf := of_decide_eq_true hin'.1
  have h2 : tf < t2 := of_decide_eq_true hin'.2
  rw [← Finset.sum_Ico_consecutive _ h1 (Nat.le_of_lt h2)]
  have hzero : ∑ t ∈ Finset.Ico (α := Nat) t1 tf,
      (if service sched j t = ρ then (suspended sched j t).toNat else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro t ht
    have hmem := Finset.mem_Ico.mp ht
    have hb := hbefore t (by simp [hmem.1, hmem.2])
    split
    · rename_i hst
      have hns : suspended sched j t = false := by
        cases hs : suspended sched j t with
        | false => rfl
        | true => simp [hs, hst] at hb
      rw [hns]
      rfl
    · rfl
  rw [hzero, Nat.zero_add]
  by_cases hle : t2 - tf ≤ job_suspension j ρ
  · exact suspension_bounded_trivial sched j t1 t2 ρ tf hin hsus hserv hle
  · exact suspension_bounded_longer_interval sched j t1 t2 ρ tf hin hsus hserv (by (try dsimp only [instant, duration, work] at *); omega)

/-- If `j` is suspended with service `ρ` somewhere in `[t1, t2)`, there is a first such instant. -/
theorem exists_some_point (j : Job) (t1 t2 : instant) (ρ : work) :
    (∃ t, decide (t ∈ List.range' t1 (t2 - t1)) = true ∧
        (suspended sched j t && decide (service sched j t = ρ)) = true) →
      ∃ t' : Nat, (decide (t1 ≤ t') && decide (t' < t2)) = true ∧ suspended sched j t' = true ∧
        service sched j t' = ρ ∧
        ∀ t0 : Nat, (decide (t1 ≤ t0) && decide (t0 < t')) = true →
          (!(suspended sched j t0 && decide (service sched j t0 = ρ))) = true := by
  intro ⟨t, hmem, hP⟩
  classical
  have hex : ∃ n, t1 ≤ n ∧ n < t2 ∧ (suspended sched j n && decide (service sched j n = ρ)) = true := by
    have := List.mem_range'_1.mp (of_decide_eq_true hmem)
    exact ⟨t, this.1, by (try dsimp only [instant, duration, work] at *); omega, hP⟩
  let t' := Nat.find hex
  have hspec := Nat.find_spec hex
  have hP' := Bool.and_eq_true_iff.mp hspec.2.2
  refine ⟨t', by simp only [Bool.and_eq_true, decide_eq_true_eq]; exact ⟨hspec.1, hspec.2.1⟩, hP'.1, of_decide_eq_true hP'.2, ?_⟩
  intro t0 hto
  have hto' := Bool.and_eq_true_iff.mp hto
  have hlt : t0 < t' := of_decide_eq_true hto'.2
  have hmin := Nat.find_min hex hlt
  have hfalse : (suspended sched j t0 && decide (service sched j t0 = ρ)) = false := by
    cases hq : (suspended sched j t0 && decide (service sched j t0 = ρ)) with
    | false => rfl
    | true =>
      exact absurd ⟨of_decide_eq_true hto'.1, by have := hspec.2.1; (try dsimp only [instant, duration, work] at *); omega, hq⟩ hmin
  rw [hfalse]
  rfl

/-- The total time `j` is suspended while having received service `ρ`, within any interval, is at most the
suspension bound `job_suspension j ρ`. -/
theorem suspension_bounded_in_interval (j : Job) (t1 t2 : instant) (ρ : work) :
    ∑ t ∈ Finset.Ico (α := Nat) t1 t2,
        (if service sched j t = ρ then (suspended sched j t).toNat else 0) ≤ job_suspension j ρ := by
  by_cases hex : ∃ t, decide (t ∈ List.range' t1 (t2 - t1)) = true ∧
      (suspended sched j t && decide (service sched j t = ρ)) = true
  · obtain ⟨tf, hin, hsus, hserv, hbefore⟩ := exists_some_point sched j t1 t2 ρ hex
    exact suspension_bounded_in_interval_aux sched j t1 t2 ρ tf hin hsus hserv hbefore
  · have hzero : ∑ t ∈ Finset.Ico (α := Nat) t1 t2,
        (if service sched j t = ρ then (suspended sched j t).toNat else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro t ht
      have hmem := Finset.mem_Ico.mp ht
      split
      · rename_i hst
        cases hs : suspended sched j t with
        | false => rfl
        | true =>
          exact absurd ⟨t, by simp [List.mem_range'_1]; (try dsimp only [instant, duration, work] at *); omega, by simp [hs, hst]⟩ hex
      · rfl
    rw [hzero]
    exact Nat.zero_le _

end Suspensions

end Prosa.Analysis.Facts.Suspension
