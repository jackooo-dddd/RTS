-- Authoritative source:
-- ProsaBuddy classic Prosa (prosabuddy commit f692cb7479780cf6009493f373a309e13165201c)
-- source: classic/model/schedule/uni/schedule.v
-- sha256: see Prosa-Shunqi/classic-prosa/comprehensive-classic/file_order.csv (rank 42)

import Prosa.Classic.Util.All
import Prosa.Classic.Model.Time
import Prosa.Classic.Model.Arrival.Basic.Task
import Prosa.Classic.Model.Arrival.Basic.Job
import Prosa.Classic.Model.Arrival.Basic.ArrivalSequence
import Prosa.Util.UnitGrowth

/-!
Uniprocessor schedules (Rocq module `UniprocessorSchedule`, which `Export`s `Time` and `ArrivalSequence`).

Representation notes (as in the accepted global `classic/model/schedule/global/basic/schedule.v`):
* `schedule Job := time -> option Job` is a reducible type definition with `Job` explicit.
* `sched t == Some j` is `decide (sched t = some j)`; the Boolean-to-`nat` coercion of `service_at` is
  `Bool.toNat`; `\sum_(a <= t < b) F t` is `∑ t ∈ Finset.Ico a b, F t`; `~~ b` in a Boolean expression is `!b`.
* Boolean tests in proposition position are `= true`; ssrnat comparisons in proposition position are the
  Nat order; chains `a <= t < b` are `(decide (a ≤ t) && decide (t < b)) = true`.
* The section-local `Let same_task j1 j2 := job_task j1 == job_task j2` is unfolded to
  `decide (job_task j1 = job_task j2) = true`.
* `[exists t : 'I_n, P t]` is `(List.finRange n).any (fun t => P t)` (ordinals coerced to `nat`).
* `unit_growth_function` is the accepted v0.6 `Prosa.Util.UnitGrowth.unit_growth_function`.
* Binder lists follow the Rocq contract: each lemma takes exactly the section variables and hypotheses Rocq
  abstracts (e.g. `job_pending_at_arrival` takes `H_jobs_must_arrive` but not `H_completed_jobs`).
-/

/- The Rocq module path is mirrored exactly (file `schedule.v` inside directory `schedule/`), which repeats a
namespace segment; Rocq abstracts some hypotheses that a proof does not use. -/
set_option linter.dupNamespace false
set_option linter.unusedVariables false

namespace Prosa.Classic.Model.Schedule.Uni.Schedule.UniprocessorSchedule

open Prosa.Classic.Model.Time.Time
open Prosa.Classic.Model.Arrival.Basic.ArrivalSequence.ArrivalSequence
open Prosa.Util.UnitGrowth (unit_growth_function exists_intermediate_point)

universe u v

local macro "omega'" : tactic =>
  `(tactic| ((try dsimp only [Prosa.Classic.Model.Time.Time.time,
    Prosa.Classic.Model.Time.Time.instant, Prosa.Classic.Model.Time.Time.duration] at *) <;>
    omega))

abbrev schedule (Job : Type u) [DecidableEq Job] := time → Option Job

def scheduled_at {Job : Type u} [DecidableEq Job] (sched : schedule Job) (j : Job) (t : time) : Bool :=
  decide (sched t = some j)

def service_at {Job : Type u} [DecidableEq Job] (sched : schedule Job) (j : Job) (t : time) : time :=
  (scheduled_at sched j t).toNat

def service_during {Job : Type u} [DecidableEq Job] (sched : schedule Job) (j : Job) (t1 t2 : time) : Nat :=
  ∑ t ∈ Finset.Ico t1 t2, service_at sched j t

def service {Job : Type u} [DecidableEq Job] (sched : schedule Job) (j : Job) (t : time) : Nat :=
  service_during sched j 0 t

def completed_by {Job : Type u} [DecidableEq Job] (job_cost : Job → time) (sched : schedule Job) (j : Job)
    (t : time) : Bool :=
  decide (job_cost j ≤ service sched j t)

def pending {Job : Type u} [DecidableEq Job] (job_arrival job_cost : Job → time) (sched : schedule Job)
    (j : Job) (t : time) : Bool :=
  has_arrived job_arrival j t && !completed_by job_cost sched j t

def pending_earlier_and_at {Job : Type u} [DecidableEq Job] (job_arrival job_cost : Job → time)
    (sched : schedule Job) (j : Job) (t : time) : Bool :=
  arrived_before job_arrival j t && !completed_by job_cost sched j t

def backlogged {Job : Type u} [DecidableEq Job] (job_arrival job_cost : Job → time) (sched : schedule Job)
    (j : Job) (t : time) : Bool :=
  pending job_arrival job_cost sched j t && !scheduled_at sched j t

def is_idle {Job : Type u} [DecidableEq Job] (sched : schedule Job) (t : time) : Bool :=
  decide (sched t = none)

def total_service_during {Job : Type u} [DecidableEq Job] (sched : schedule Job) (t1 t2 : time) : Nat :=
  ∑ t ∈ Finset.Ico t1 t2, (!is_idle sched t).toNat

def total_service {Job : Type u} [DecidableEq Job] (sched : schedule Job) (t2 : time) : Nat :=
  total_service_during sched 0 t2

def sequential_jobs {Job : Type u} [DecidableEq Job] (job_arrival job_cost : Job → time)
    (sched : schedule Job) {Task : Type v} [DecidableEq Task] (job_task : Job → Task) : Prop :=
  ∀ j1 j2 t,
    decide (job_task j1 = job_task j2) = true →
    job_arrival j1 < job_arrival j2 →
    scheduled_at sched j2 t = true →
    completed_by job_cost sched j1 t = true

theorem scheduler_executes_job_with_earliest_arrival {Job : Type u} [DecidableEq Job]
    (job_arrival job_cost : Job → time) (sched : schedule Job) {Task : Type v} [DecidableEq Task]
    (job_task : Job → Task) (H_sequential_jobs : sequential_jobs job_arrival job_cost sched job_task) :
    ∀ j1 j2 t,
      decide (job_task j1 = job_task j2) = true →
      (!completed_by job_cost sched j2 t) = true →
      scheduled_at sched j1 t = true →
      job_arrival j1 ≤ job_arrival j2 := by
  intro j1 j2 t TSK NCOMPL SCHED
  by_contra ARR
  have SEQ := H_sequential_jobs j2 j1 t (by simpa [eq_comm] using TSK) (by omega') SCHED
  simp [SEQ] at NCOMPL

def jobs_come_from_arrival_sequence {Job : Type u} [DecidableEq Job] (sched : schedule Job)
    (arr_seq : arrival_sequence Job) : Prop :=
  ∀ j t, scheduled_at sched j t = true → arrives_in arr_seq j

def jobs_must_arrive_to_execute {Job : Type u} [DecidableEq Job] (job_arrival : Job → time)
    (sched : schedule Job) : Prop :=
  ∀ j t, scheduled_at sched j t = true → has_arrived job_arrival j t = true

def completed_jobs_dont_execute {Job : Type u} [DecidableEq Job] (job_cost : Job → time)
    (sched : schedule Job) : Prop :=
  ∀ j t, service sched j t ≤ job_cost j

def remaining_cost {Job : Type u} [DecidableEq Job] (job_cost : Job → time) (sched : schedule Job) (j : Job)
    (t : time) : Nat :=
  job_cost j - service sched j t

/-- LEAN_HELPER: service up to `t + 1` adds the service at `t`. -/
private theorem service_succ {Job : Type u} [DecidableEq Job] (sched : schedule Job) (j : Job) (t : time) :
    service sched j (t + 1) = service sched j t + service_at sched j t := by
  unfold service service_during
  exact Finset.sum_Ico_succ_top (Nat.zero_le t) _

/-- LEAN_HELPER: the instantaneous service is `1` exactly when the job is scheduled. -/
private theorem service_at_eq {Job : Type u} [DecidableEq Job] (sched : schedule Job) (j : Job) (t : time) :
    service_at sched j t = if scheduled_at sched j t then 1 else 0 := by
  unfold service_at; cases scheduled_at sched j t <;> rfl

theorem service_at_most_one {Job : Type u} [DecidableEq Job] (sched : schedule Job) (j : Job) :
    ∀ t, service_at sched j t ≤ 1 := by
  intro t; rw [service_at_eq]; split <;> omega'

theorem cumulative_service_le_delta {Job : Type u} [DecidableEq Job] (sched : schedule Job) (j : Job) :
    ∀ t delta, service_during sched j t (t + delta) ≤ delta := by
  intro t delta
  unfold service_during
  calc ∑ x ∈ Finset.Ico t (t + delta), service_at sched j x
      ≤ ∑ _x ∈ Finset.Ico t (t + delta), 1 :=
        Finset.sum_le_sum fun x _ => service_at_most_one sched j x
    _ = delta := by simp

theorem scheduled_implies_positive_remaining_cost {Job : Type u} [DecidableEq Job] (job_cost : Job → time)
    (sched : schedule Job) (j : Job) (H_completed_jobs : completed_jobs_dont_execute job_cost sched) :
    ∀ t, scheduled_at sched j t = true → 0 < remaining_cost job_cost sched j t := by
  intro t SCHED
  have h := H_completed_jobs j (t + 1)
  rw [service_succ, service_at_eq, if_pos SCHED] at h
  unfold remaining_cost
  omega'

theorem completion_monotonic {Job : Type u} [DecidableEq Job] (job_cost : Job → time) (sched : schedule Job)
    (j : Job) :
    ∀ t t' : Nat, t ≤ t' → completed_by job_cost sched j t = true → completed_by job_cost sched j t' = true := by
  intro t t' LE COMPt
  simp only [completed_by, decide_eq_true_eq] at COMPt ⊢
  apply Nat.le_trans COMPt
  unfold service service_during
  exact Finset.sum_le_sum_of_subset (Finset.Ico_subset_Ico (Nat.le_refl 0) LE)

theorem completed_implies_not_scheduled {Job : Type u} [DecidableEq Job] (job_cost : Job → time)
    (sched : schedule Job) (j : Job) (H_completed_jobs : completed_jobs_dont_execute job_cost sched) :
    ∀ t, completed_by job_cost sched j t = true → (!scheduled_at sched j t) = true := by
  intro t COMPLETED
  simp only [completed_by, decide_eq_true_eq] at COMPLETED
  cases SCHED : scheduled_at sched j t
  · rfl
  · have BUG := H_completed_jobs j (t + 1)
    rw [service_succ, service_at_eq, if_pos SCHED] at BUG
    omega'

theorem scheduled_implies_not_completed {Job : Type u} [DecidableEq Job] (job_cost : Job → time)
    (sched : schedule Job) (j : Job) (H_completed_jobs : completed_jobs_dont_execute job_cost sched) :
    ∀ t, scheduled_at sched j t = true → (!completed_by job_cost sched j t) = true := by
  intro t SCHED
  cases COMPL : completed_by job_cost sched j t
  · rfl
  · have := completed_implies_not_scheduled job_cost sched j H_completed_jobs t COMPL
    simp [SCHED] at this

theorem cumulative_service_le_job_cost {Job : Type u} [DecidableEq Job] (job_cost : Job → time)
    (sched : schedule Job) (j : Job) (H_completed_jobs : completed_jobs_dont_execute job_cost sched) :
    ∀ t t', service_during sched j t t' ≤ job_cost j := by
  intro t t'
  apply Nat.le_trans _ (H_completed_jobs j t')
  unfold service service_during
  exact Finset.sum_le_sum_of_subset (Finset.Ico_subset_Ico (Nat.zero_le t) (Nat.le_refl t'))

theorem job_doesnt_complete_before_remaining_cost {Job : Type u} [DecidableEq Job] (job_cost : Job → time)
    (sched : schedule Job) (j : Job) (H_completed_jobs : completed_jobs_dont_execute job_cost sched) :
    ∀ t, (!completed_by job_cost sched j t) = true →
      (!completed_by job_cost sched j (t + remaining_cost job_cost sched j t - 1)) = true := by
  intro t GT0
  simp only [completed_by, Bool.not_eq_true', decide_eq_false_iff_not, Nat.not_le] at GT0 ⊢
  unfold remaining_cost
  -- the service in `[t, t + δ - 1)` is at most `δ - 1`
  set δ := job_cost j - service sched j t with hδ
  have hδpos : 0 < δ := by omega'
  have hsplit : service sched j (t + δ - 1) = service sched j t + service_during sched j t (t + (δ - 1)) := by
    unfold service service_during
    have : t + δ - 1 = t + (δ - 1) := by omega'
    rw [this, ← Finset.sum_Ico_consecutive _ (Nat.zero_le t) (Nat.le_add_right t (δ - 1))]
  have hle := cumulative_service_le_delta sched j t (δ - 1)
  rw [hsplit]
  omega'

theorem completed_implies_scheduled_before {Job : Type u} [DecidableEq Job] (job_arrival job_cost : Job → time)
    (sched : schedule Job) (j : Job) (H_positive_cost : 0 < job_cost j)
    (H_jobs_must_arrive : jobs_must_arrive_to_execute job_arrival sched) :
    ∀ t, completed_by job_cost sched j t = true →
      ∃ t', (decide (job_arrival j ≤ t') && decide (t' < t)) = true ∧ scheduled_at sched j t' = true := by
  intro t
  induction t with
  | zero =>
    intro COMPL
    simp [completed_by, service, service_during] at COMPL
    omega'
  | succ t IH =>
    intro COMPL
    cases COMPLatt : completed_by job_cost sched j t
    · simp only [completed_by, decide_eq_true_eq] at COMPL
      simp only [completed_by, decide_eq_false_iff_not, Nat.not_le] at COMPLatt
      rw [service_succ, service_at_eq] at COMPL
      split at COMPL
      · rename_i SCHED
        have ARR := H_jobs_must_arrive j t SCHED
        simp only [has_arrived, decide_eq_true_eq] at ARR
        exact ⟨t, by simp [ARR], SCHED⟩
      · omega'
    · obtain ⟨t', H, SCHED⟩ := IH COMPLatt
      simp only [Bool.and_eq_true, decide_eq_true_eq] at H
      exact ⟨t', by simp [H.1]; omega', SCHED⟩

theorem service_before_job_arrival_zero {Job : Type u} [DecidableEq Job] (job_arrival : Job → time)
    (sched : schedule Job) (H_jobs_must_arrive : jobs_must_arrive_to_execute job_arrival sched) (j : Job) :
    ∀ t : Nat, t < job_arrival j → service_at sched j t = 0 := by
  intro t LT
  rw [service_at_eq]
  split
  · rename_i SCHED
    have := H_jobs_must_arrive j t SCHED
    simp only [has_arrived, decide_eq_true_eq] at this
    omega'
  · rfl

theorem cumulative_service_before_job_arrival_zero {Job : Type u} [DecidableEq Job] (job_arrival : Job → time)
    (sched : schedule Job) (H_jobs_must_arrive : jobs_must_arrive_to_execute job_arrival sched) (j : Job) :
    ∀ t1 t2 : Nat, t2 ≤ job_arrival j → ∑ i ∈ Finset.Ico t1 t2, service_at sched j i = 0 := by
  intro t1 t2 LE
  apply Finset.sum_eq_zero
  intro i hi
  rw [Finset.mem_Ico] at hi
  exact service_before_job_arrival_zero job_arrival sched H_jobs_must_arrive j i (by omega')

theorem ignore_service_before_arrival {Job : Type u} [DecidableEq Job] (job_arrival : Job → time)
    (sched : schedule Job) (H_jobs_must_arrive : jobs_must_arrive_to_execute job_arrival sched) (j : Job) :
    ∀ t1 t2 : Nat, t1 ≤ job_arrival j → job_arrival j ≤ t2 →
      ∑ t ∈ Finset.Ico t1 t2, service_at sched j t = ∑ t ∈ Finset.Ico (job_arrival j) t2, service_at sched j t := by
  intro t1 t2 LE1 GE2
  rw [← Finset.sum_Ico_consecutive _ LE1 GE2,
    cumulative_service_before_job_arrival_zero job_arrival sched H_jobs_must_arrive j t1 (job_arrival j)
      (Nat.le_refl _), Nat.zero_add]

theorem scheduled_implies_pending {Job : Type u} [DecidableEq Job] (job_arrival job_cost : Job → time)
    (sched : schedule Job) (H_jobs_must_arrive : jobs_must_arrive_to_execute job_arrival sched)
    (H_completed_jobs : completed_jobs_dont_execute job_cost sched) (j : Job) :
    ∀ t, scheduled_at sched j t = true → pending job_arrival job_cost sched j t = true := by
  intro t SCHED
  have h1 := H_jobs_must_arrive j t SCHED
  have h2 := scheduled_implies_not_completed job_cost sched j H_completed_jobs t SCHED
  simp only [pending, h1, h2, Bool.true_and]

theorem job_pending_at_arrival {Job : Type u} [DecidableEq Job] (job_arrival job_cost : Job → time)
    (sched : schedule Job) (H_jobs_must_arrive : jobs_must_arrive_to_execute job_arrival sched) (j : Job)
    (arr_seq : arrival_sequence Job) :
    arrives_in arr_seq j → 0 < job_cost j → pending job_arrival job_cost sched j (job_arrival j) = true := by
  intro _ POS
  have h0 : service sched j (job_arrival j) = 0 := by
    unfold service service_during
    exact cumulative_service_before_job_arrival_zero job_arrival sched H_jobs_must_arrive j 0 (job_arrival j)
      (Nat.le_refl _)
  simp only [pending, has_arrived, completed_by, h0, Nat.le_refl, decide_true, Bool.true_and,
    Bool.not_eq_true', decide_eq_false_iff_not, Nat.not_le]
  omega'

theorem only_one_job_scheduled {Job : Type u} [DecidableEq Job] (sched : schedule Job) (j1 j2 : Job) :
    ∀ t, scheduled_at sched j1 t = true → scheduled_at sched j2 t = true → j1 = j2 := by
  intro t S1 S2
  simp only [scheduled_at, decide_eq_true_eq] at S1 S2
  rw [S1] at S2
  exact Option.some.inj S2

theorem service_is_a_step_function {Job : Type u} [DecidableEq Job] (sched : schedule Job) :
    ∀ j, unit_growth_function (service sched j) := by
  intro j t
  rw [service_succ]
  exact Nat.add_le_add_left (service_at_most_one sched j t) _

theorem exists_intermediate_service {Job : Type u} [DecidableEq Job] (sched : schedule Job) (j : Job) (t : time)
    (s0 : time) (H_less_than_s : s0 < service sched j t) :
    ∃ t0, t0 < t ∧ service sched j t0 = s0 := by
  obtain ⟨x, hx, hfx⟩ := exists_intermediate_point _ (service_is_a_step_function sched j) 0 t (Nat.zero_le t) s0
    ⟨by simp [service, service_during], H_less_than_s⟩
  exact ⟨x, hx.2, hfx⟩

theorem scheduled_at_earlier_time {Job : Type u} [DecidableEq Job] (sched : schedule Job) :
    ∀ j t, 0 < service sched j t → ∃ t0, t0 < t ∧ scheduled_at sched j t0 = true := by
  intro j t GT
  unfold service service_during at GT
  obtain ⟨t0, ht0, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero (Nat.pos_iff_ne_zero.mp GT)
  rw [Finset.mem_Ico] at ht0
  refine ⟨t0, ht0.2, ?_⟩
  rw [service_at_eq] at hne
  split at hne
  · assumption
  · exact absurd rfl hne

theorem cumulative_service_implies_scheduled {Job : Type u} [DecidableEq Job] (sched : schedule Job) (j : Job)
    (t1 t2 : time) (H_service_not_zero : 0 < service_during sched j t1 t2) :
    ∃ t, (decide (t1 ≤ t) && decide (t < t2)) = true ∧ scheduled_at sched j t = true := by
  unfold service_during at H_service_not_zero
  obtain ⟨t, ht, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero (Nat.pos_iff_ne_zero.mp H_service_not_zero)
  rw [Finset.mem_Ico] at ht
  refine ⟨t, by simp [ht.1, ht.2], ?_⟩
  rw [service_at_eq] at hne
  split at hne
  · assumption
  · exact absurd rfl hne

/-- LEAN_HELPER: `[exists t : 'I_n, scheduled_at sched j t]` as a Prop. -/
private theorem any_finRange_iff {Job : Type u} [DecidableEq Job] (sched : schedule Job) (j : Job) (n : Nat) :
    (List.finRange n).any (fun t => scheduled_at sched j t) = true ↔ ∃ t, t < n ∧ scheduled_at sched j t = true := by
  simp only [List.any_eq_true, List.mem_finRange, true_and]
  constructor
  · rintro ⟨t, h⟩; exact ⟨t.val, t.isLt, h⟩
  · rintro ⟨t, ht, h⟩; exact ⟨⟨t, ht⟩, h⟩

/-- LEAN_HELPER: being scheduled at `t0 < t'` strictly increases the service from `t0` to `t'`. -/
private theorem service_lt_of_scheduled {Job : Type u} [DecidableEq Job] (sched : schedule Job) (j : Job)
    (t0 t' : Nat) (hlt : t0 < t') (SCHED : scheduled_at sched j t0 = true) :
    service sched j t0 < service sched j t' := by
  have h1 : service sched j (t0 + 1) = service sched j t0 + 1 := by
    rw [service_succ, service_at_eq, if_pos SCHED]
  have h2 : service sched j (t0 + 1) ≤ service sched j t' := by
    unfold service service_during
    exact Finset.sum_le_sum_of_subset (Finset.Ico_subset_Ico (Nat.le_refl 0) hlt)
  omega'

theorem same_service_implies_scheduled_at_earlier_times {Job : Type u} [DecidableEq Job] (sched : schedule Job)
    (j : Job) (t1 t2 : time) (H_same_service : service sched j t1 = service sched j t2) :
    (List.finRange t1).any (fun t => scheduled_at sched j t) =
      (List.finRange t2).any (fun t' => scheduled_at sched j t') := by
  have key : ∀ a b : Nat, a ≤ b → service sched j a = service sched j b →
      ((∃ t, t < a ∧ scheduled_at sched j t = true) ↔ (∃ t, t < b ∧ scheduled_at sched j t = true)) := by
    intro a b LE SERV
    constructor
    · rintro ⟨t0, h, s⟩; exact ⟨t0, by omega', s⟩
    · rintro ⟨t0, h, s⟩
      by_cases hlt : t0 < a
      · exact ⟨t0, hlt, s⟩
      · exfalso
        have := service_lt_of_scheduled sched j t0 b h s
        have hmono : service sched j a ≤ service sched j t0 := by
          unfold service service_during
          exact Finset.sum_le_sum_of_subset (Finset.Ico_subset_Ico (Nat.le_refl 0) (by omega'))
        omega'
  apply Bool.eq_iff_iff.mpr
  rw [any_finRange_iff, any_finRange_iff]
  rcases Nat.le_total t1 t2 with h | h
  · exact key t1 t2 h H_same_service
  · exact (key t2 t1 h H_same_service.symm).symm

end Prosa.Classic.Model.Schedule.Uni.Schedule.UniprocessorSchedule
