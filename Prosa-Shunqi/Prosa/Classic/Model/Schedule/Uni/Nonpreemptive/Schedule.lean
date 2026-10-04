-- Authoritative source:
-- ProsaBuddy classic Prosa (prosabuddy commit f692cb7479780cf6009493f373a309e13165201c)
-- source: classic/model/schedule/uni/nonpreemptive/schedule.v
-- sha256: see Prosa-Shunqi/classic-prosa/comprehensive-classic/file_order.csv (rank 56)

import Prosa.Classic.Util.All
import Prosa.Classic.Model.Arrival.Basic.Job
import Prosa.Classic.Model.Schedule.Uni.Schedule

/-!
Nonpreemptive uniprocessor schedules (Rocq module `NonpreemptiveSchedule`, which `Export`s
`UniprocessorSchedule`).

Representation notes: Boolean tests in proposition position are `= true`; `~~ b` is `(!b) = true`; Boolean
chains `a <= x <= b` / `a <= x < b` in proposition position are `decide`-chains `= true`; the section-local
`Let`s (`job_completed_by`, `job_remaining_cost`) are unfolded. Binder lists follow the Rocq contract
(e.g. `subh3` takes no section variable; `in_nonpreemption_schedule_preemption_implies_completeness` does not
take `H_completed_jobs_dont_execute`).
-/

set_option linter.dupNamespace false
set_option linter.unusedVariables false

namespace Prosa.Classic.Model.Schedule.Uni.Nonpreemptive.Schedule.NonpreemptiveSchedule

open Prosa.Classic.Model.Time.Time
open Prosa.Classic.Model.Schedule.Uni.Schedule.UniprocessorSchedule

universe u

local macro "omega'" : tactic =>
  `(tactic| ((try dsimp only [Prosa.Classic.Model.Time.Time.time,
    Prosa.Classic.Model.Time.Time.instant, Prosa.Classic.Model.Time.Time.duration] at *) <;>
    omega))

def is_nonpreemptive_schedule {Job : Type u} [DecidableEq Job] (job_cost : Job → time) (sched : schedule Job) :
    Prop :=
  ∀ j t t', t ≤ t' → scheduled_at sched j t = true → (!completed_by job_cost sched j t') = true →
    scheduled_at sched j t' = true

theorem subh3 : ∀ m n p : Nat, m + p ≤ n → m ≤ n - p := by
  intro m n p h; omega

/-- LEAN_HELPER: service up to `t + 1` adds the service at `t` (as in the uniprocessor schedule module). -/
private theorem service_succ' {Job : Type u} [DecidableEq Job] (sched : schedule Job) (j : Job) (t : time) :
    service sched j (t + 1) = service sched j t + (scheduled_at sched j t).toNat := by
  unfold service service_during
  exact Finset.sum_Ico_succ_top (Nat.zero_le t) _

theorem continuity_of_nonpreemptive_scheduling {Job : Type u} [DecidableEq Job] (job_cost : Job → time)
    (sched : schedule Job) (H_nonpreemptive : is_nonpreemptive_schedule job_cost sched) (j : Job)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched) :
    ∀ t t1 t2 : Nat, (decide (t1 ≤ t) && decide (t ≤ t2)) = true →
      scheduled_at sched j t1 = true → scheduled_at sched j t2 = true → scheduled_at sched j t = true := by
  intro t t1 t2 H S1 S2
  simp only [Bool.and_eq_true, decide_eq_true_eq] at H
  apply H_nonpreemptive j t1 t H.1 S1
  cases hc : completed_by job_cost sched j t
  · rfl
  · have := completion_monotonic job_cost sched j t t2 H.2 hc
    have := scheduled_implies_not_completed job_cost sched j H_completed_jobs_dont_execute t2 S2
    simp_all

theorem in_nonpreemption_schedule_preemption_implies_completeness {Job : Type u} [DecidableEq Job]
    (job_cost : Job → time) (sched : schedule Job) (H_nonpreemptive : is_nonpreemptive_schedule job_cost sched)
    (j : Job) :
    ∀ t t' : Nat, t ≤ t' → scheduled_at sched j t = true → (!scheduled_at sched j t') = true →
      completed_by job_cost sched j t' = true := by
  intro t t' LE SCHED NS
  cases hc : completed_by job_cost sched j t'
  · have := H_nonpreemptive j t t' LE SCHED (by simp [hc])
    simp [this] at NS
  · rfl

/-- LEAN_HELPER: from a scheduled instant, the job executes continuously until its remaining cost is used. -/
private theorem runs_to_completion {Job : Type u} [DecidableEq Job] (job_cost : Job → time) (sched : schedule Job)
    (H_nonpreemptive : is_nonpreemptive_schedule job_cost sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched) (j : Job) (t : time)
    (SCHED : scheduled_at sched j t = true) :
    ∀ k, k ≤ remaining_cost job_cost sched j t →
      service sched j (t + k) = service sched j t + k ∧
        (k < remaining_cost job_cost sched j t → scheduled_at sched j (t + k) = true) := by
  have NC := scheduled_implies_not_completed job_cost sched j H_completed_jobs_dont_execute t SCHED
  simp only [completed_by, Bool.not_eq_true', decide_eq_false_iff_not, Nat.not_le] at NC
  intro k
  induction k with
  | zero =>
    intro _
    exact ⟨by simp, fun _ => by simpa using SCHED⟩
  | succ k ih =>
    intro hk
    obtain ⟨hs, _⟩ := ih (by omega)
    have hsched : scheduled_at sched j (t + k) = true := by
      apply H_nonpreemptive j t (t + k) (Nat.le_add_right t k) SCHED
      simp only [completed_by, Bool.not_eq_true', decide_eq_false_iff_not, Nat.not_le, hs]
      unfold remaining_cost at hk
      omega'
    refine ⟨?_, ?_⟩
    · rw [← Nat.add_assoc, service_succ', hs, hsched]; simp; omega
    · intro hlt
      apply H_nonpreemptive j t (t + (k + 1)) (Nat.le_add_right t _) SCHED
      have hs' : service sched j (t + (k + 1)) = service sched j t + (k + 1) := by
        rw [← Nat.add_assoc, service_succ', hs, hsched]; simp; omega
      simp only [completed_by, Bool.not_eq_true', decide_eq_false_iff_not, Nat.not_le, hs']
      unfold remaining_cost at hlt
      omega'

theorem job_completes_after_remaining_cost {Job : Type u} [DecidableEq Job] (job_cost : Job → time)
    (sched : schedule Job) (H_nonpreemptive : is_nonpreemptive_schedule job_cost sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched) :
    ∀ j t, scheduled_at sched j t = true →
      completed_by job_cost sched j (t + remaining_cost job_cost sched j t) = true := by
  intro j t SCHED
  obtain ⟨hs, _⟩ := runs_to_completion job_cost sched H_nonpreemptive H_completed_jobs_dont_execute j t SCHED
    (remaining_cost job_cost sched j t) (Nat.le_refl _)
  simp only [completed_by, decide_eq_true_eq, hs]
  unfold remaining_cost
  omega'

/-- LEAN_HELPER: the first instant at which `j` is scheduled is `t - service sched j t`. -/
private theorem first_scheduled {Job : Type u} [DecidableEq Job] (job_cost : Job → time) (sched : schedule Job)
    (H_nonpreemptive : is_nonpreemptive_schedule job_cost sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched) (j : Job) (t : time)
    (SCHED : scheduled_at sched j t = true) :
    t - service sched j t ≤ t ∧
      (∀ x, x < t - service sched j t → scheduled_at sched j x = false) ∧
      (∀ x, t - service sched j t ≤ x → x ≤ t → scheduled_at sched j x = true) := by
  classical
  have hex : ∃ x, x ≤ t ∧ scheduled_at sched j x = true := ⟨t, Nat.le_refl t, SCHED⟩
  set t0 := Nat.find hex with ht0
  have h0 : t0 ≤ t ∧ scheduled_at sched j t0 = true := Nat.find_spec hex
  have before : ∀ x, x < t0 → scheduled_at sched j x = false := by
    intro x hx
    cases hsx : scheduled_at sched j x
    · rfl
    · exact absurd ⟨by omega', hsx⟩ (Nat.find_min hex hx)
  have during : ∀ x, t0 ≤ x → x ≤ t → scheduled_at sched j x = true := fun x h1 h2 =>
    continuity_of_nonpreemptive_scheduling job_cost sched H_nonpreemptive j H_completed_jobs_dont_execute x t0 t
      (by simp [h1, h2]) h0.2 SCHED
  have hserv : service sched j t = t - t0 := by
    unfold service service_during
    rw [← Finset.sum_Ico_consecutive _ (Nat.zero_le t0) h0.1]
    have hz : ∑ x ∈ Finset.Ico 0 t0, service_at sched j x = 0 :=
      Finset.sum_eq_zero (fun x hx => by
        rw [Finset.mem_Ico] at hx; simp [service_at, before x hx.2])
    have ho : ∑ x ∈ Finset.Ico t0 t, service_at sched j x = ∑ _x ∈ Finset.Ico t0 t, 1 :=
      Finset.sum_congr rfl (fun x hx => by
        rw [Finset.mem_Ico] at hx; simp [service_at, during x hx.1 (Nat.le_of_lt hx.2)])
    rw [hz, ho]; simp
  have heq : t - service sched j t = t0 := by rw [hserv]; omega'
  rw [heq]
  exact ⟨h0.1, before, during⟩

theorem j_is_scheduled_at_t_minus_service {Job : Type u} [DecidableEq Job] (job_cost : Job → time)
    (sched : schedule Job) (H_nonpreemptive : is_nonpreemptive_schedule job_cost sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched) (j : Job) (t : time)
    (H_j_is_scheduled_at_t : scheduled_at sched j t = true) :
    scheduled_at sched j (t - service sched j t) = true := by
  obtain ⟨hle, _, during⟩ := first_scheduled job_cost sched H_nonpreemptive H_completed_jobs_dont_execute j t
    H_j_is_scheduled_at_t
  exact during _ (Nat.le_refl _) hle

theorem j_is_not_scheduled_at_t_minus_service_minus_one {Job : Type u} [DecidableEq Job] (job_cost : Job → time)
    (sched : schedule Job) (H_nonpreemptive : is_nonpreemptive_schedule job_cost sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched) (j : Job) (t : time)
    (H_j_is_scheduled_at_t : scheduled_at sched j t = true) :
    0 < t - service sched j t → (!scheduled_at sched j (t - service sched j t - 1)) = true := by
  intro GT
  obtain ⟨_, before, _⟩ := first_scheduled job_cost sched H_nonpreemptive H_completed_jobs_dont_execute j t
    H_j_is_scheduled_at_t
  rw [before _ (by omega')]; rfl

theorem j_is_not_scheduled_earlier_t_minus_service {Job : Type u} [DecidableEq Job] (job_cost : Job → time)
    (sched : schedule Job) (H_nonpreemptive : is_nonpreemptive_schedule job_cost sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched) (j : Job) (t : time)
    (H_j_is_scheduled_at_t : scheduled_at sched j t = true) :
    ∀ t' : Nat, t' < t - service sched j t → (!scheduled_at sched j t') = true := by
  intro t' GT
  obtain ⟨_, before, _⟩ := first_scheduled job_cost sched H_nonpreemptive H_completed_jobs_dont_execute j t
    H_j_is_scheduled_at_t
  simp [before _ GT]

theorem j_is_scheduled_at_t_plus_remaining_cost_minus_one {Job : Type u} [DecidableEq Job]
    (job_cost : Job → time) (sched : schedule Job) (H_nonpreemptive : is_nonpreemptive_schedule job_cost sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched) (j : Job) (t : time)
    (H_j_is_scheduled_at_t : scheduled_at sched j t = true) :
    scheduled_at sched j (t + remaining_cost job_cost sched j t - 1) = true := by
  have hpos := scheduled_implies_positive_remaining_cost job_cost sched j H_completed_jobs_dont_execute t
    H_j_is_scheduled_at_t
  obtain ⟨_, hs⟩ := runs_to_completion job_cost sched H_nonpreemptive H_completed_jobs_dont_execute j t
    H_j_is_scheduled_at_t (remaining_cost job_cost sched j t - 1) (by omega)
  have := hs (by omega)
  have heq : t + remaining_cost job_cost sched j t - 1 = t + (remaining_cost job_cost sched j t - 1) := by omega'
  rw [heq]; exact this

theorem j_is_not_scheduled_after_t_plus_remaining_cost_minus_one {Job : Type u} [DecidableEq Job]
    (job_cost : Job → time) (sched : schedule Job) (H_nonpreemptive : is_nonpreemptive_schedule job_cost sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched) (j : Job) (t : time)
    (H_j_is_scheduled_at_t : scheduled_at sched j t = true) :
    ∀ t' : Nat, t + remaining_cost job_cost sched j t ≤ t' → (!scheduled_at sched j t') = true := by
  intro t' GE
  have COMP := job_completes_after_remaining_cost job_cost sched H_nonpreemptive H_completed_jobs_dont_execute j t
    H_j_is_scheduled_at_t
  exact completed_implies_not_scheduled job_cost sched j H_completed_jobs_dont_execute t'
    (completion_monotonic job_cost sched j _ t' GE COMP)

theorem nonpreemptive_executing_interval {Job : Type u} [DecidableEq Job] (job_cost : Job → time)
    (sched : schedule Job) (H_nonpreemptive : is_nonpreemptive_schedule job_cost sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched) (j : Job) (t : time)
    (H_j_is_scheduled_at_t : scheduled_at sched j t = true) :
    ∀ t' : Nat,
      (decide (t - service sched j t ≤ t') && decide (t' < t + remaining_cost job_cost sched j t)) = true →
      scheduled_at sched j t' = true := by
  intro t' H
  simp only [Bool.and_eq_true, decide_eq_true_eq] at H
  obtain ⟨hle, _, during⟩ := first_scheduled job_cost sched H_nonpreemptive H_completed_jobs_dont_execute j t
    H_j_is_scheduled_at_t
  rcases Nat.le_total t' t with h | h
  · exact during t' H.1 h
  · obtain ⟨_, hs⟩ := runs_to_completion job_cost sched H_nonpreemptive H_completed_jobs_dont_execute j t
      H_j_is_scheduled_at_t (t' - t) (by omega')
    have := hs (by omega')
    have heq : t + (t' - t) = t' := by omega'
    rw [heq] at this; exact this

end Prosa.Classic.Model.Schedule.Uni.Nonpreemptive.Schedule.NonpreemptiveSchedule
