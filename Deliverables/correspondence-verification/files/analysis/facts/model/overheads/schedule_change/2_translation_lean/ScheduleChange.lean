-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/facts/model/overheads/schedule_change.v

import Prosa.Analysis.Definitions.Overheads.ScheduleChange
import Prosa.Analysis.Facts.Model.Overheads.Schedule

namespace Prosa.Analysis.Facts.Model.Overheads.ScheduleChange

open Prosa.Behavior.Job
open Prosa.Behavior.Schedule
open Prosa.Behavior.Time
open Prosa.Model.Processor.Overheads
open Prosa.Analysis.Definitions.Overheads.ScheduleChange
open Prosa.Util.List

/-! Basic properties of the number of schedule changes of a schedule with explicit
overheads, and of the predicate `scheduled_job_invariant`. -/

private theorem mem_index_iota' {a b t : Nat} : t ∈ index_iota a b ↔ a ≤ t ∧ t < b := by
  simp only [index_iota, List.mem_range']
  constructor
  · rintro ⟨i, hi, rfl⟩; omega
  · rintro ⟨h1, h2⟩; exact ⟨t - a, by omega, by omega⟩

/-- The number of schedule changes over `[t1, t2)` is the number over `[t1, t)` plus the
number over `[t, t2)`. -/
theorem number_schedule_changes_cat {Job : JobType} [DecidableEq Job]
    (sched : schedule (processor_state Job)) (t t1 t2 : instant) :
    (decide (t1 ≤ t) && decide (t ≤ t2)) = true →
    number_schedule_changes sched t1 t2 =
      number_schedule_changes sched t1 t + number_schedule_changes sched t t2 := by
  intro h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  unfold number_schedule_changes
  rw [index_iota_cat t t1 t2 h, List.countP_append]

/-- If `[t1, t2)` contains `k > 0` schedule changes, the first of them exists. -/
theorem first_schedule_change_exists {Job : JobType} [DecidableEq Job]
    (sched : schedule (processor_state Job)) (t1 t2 : instant) (k : Nat) :
    0 < k → number_schedule_changes sched t1 t2 = k →
    ∃ t : Nat, (decide (t1 ≤ t) && decide (t < t2)) = true ∧ schedule_change sched t = true ∧
      number_schedule_changes sched t1 t = 0 ∧ number_schedule_changes sched t t2 = k := by
  intro hk hnum
  dsimp only [instant] at *
  have hex : ∃ t, t1 ≤ t ∧ t < t2 ∧ schedule_change sched t = true := by
    have hpos : 0 < (index_iota t1 t2).countP (schedule_change sched) := by
      unfold number_schedule_changes at hnum; ((try dsimp only [instant] at *); omega)
    obtain ⟨a, ha, hsc⟩ := List.countP_pos_iff.1 hpos
    exact ⟨a, (mem_index_iota'.1 ha).1, (mem_index_iota'.1 ha).2, hsc⟩
  classical
  let t := Nat.find hex
  have ht : t1 ≤ t ∧ t < t2 ∧ schedule_change sched t = true := Nat.find_spec hex
  have hmin : ∀ s, s < t → ¬ (t1 ≤ s ∧ s < t2 ∧ schedule_change sched s = true) :=
    fun s hs => Nat.find_min hex hs
  have hzero : number_schedule_changes sched t1 t = 0 := by
    unfold number_schedule_changes
    rw [List.countP_eq_zero]
    intro a ha hsc
    have ha' := mem_index_iota'.1 ha
    exact hmin a ha'.2 ⟨ha'.1, by ((try dsimp only [instant] at *); omega), hsc⟩
  refine ⟨t, ?_, ht.2.2, hzero, ?_⟩
  · simp [ht.1, ht.2.1]
  · have hcat := number_schedule_changes_cat sched t t1 t2 (by simp [ht.1, Nat.le_of_lt ht.2.1])
    ((try dsimp only [instant] at *); omega)

/-- Widening the interval can only increase the number of schedule changes. -/
theorem number_schedule_changes_widen {Job : JobType} [DecidableEq Job]
    (sched : schedule (processor_state Job)) (t1 t2 t1' t2' : instant) :
    t1 ≤ t1' → t2' ≤ t2 →
    number_schedule_changes sched t1' t2' ≤ number_schedule_changes sched t1 t2 := by
  intro h1 h2
  dsimp only [instant] at *
  by_cases hle : t2' ≤ t1'
  · have : index_iota t1' t2' = [] := by simp [index_iota, Nat.sub_eq_zero_of_le hle]
    simp [number_schedule_changes, this]
  · have hA := number_schedule_changes_cat sched t1' t1 t2
      (by simp only [Bool.and_eq_true, decide_eq_true_eq]; exact ⟨h1, by ((try dsimp only [instant] at *); omega)⟩)
    have hB := number_schedule_changes_cat sched t2' t1' t2
      (by simp only [Bool.and_eq_true, decide_eq_true_eq]; exact ⟨by ((try dsimp only [instant] at *); omega), h2⟩)
    ((try dsimp only [instant] at *); omega)

/-- If the scheduled job is `oj1` throughout `[t1, t)`, `oj2` throughout `[t, t2)`, and no
schedule change happens at `t`, then `oj1 = oj2`. -/
theorem same_scheduled_state_merge {Job : JobType} [DecidableEq Job]
    (sched : schedule (processor_state Job)) (t1 t2 t : instant) (oj1 oj2 : Option Job) :
    (decide (t1 < t) && decide (t < t2)) = true → (!schedule_change sched t) = true →
    scheduled_job_invariant sched oj1 t1 t = true →
    scheduled_job_invariant sched oj2 t t2 = true → oj1 = oj2 := by
  intro hrange hnc h1 h2
  dsimp only [instant] at *
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hrange
  unfold scheduled_job_invariant at h1 h2
  rw [List.all_eq_true] at h1 h2
  have hp : Nat.pred t = t - 1 := Nat.pred_eq_sub_one
  have e1 := h1 (Nat.pred t) (mem_index_iota'.2 (show t1 ≤ Nat.pred t ∧ Nat.pred t < t by
    rw [hp]; ((try dsimp only [instant] at *); omega)))
  have e2 := h2 t (mem_index_iota'.2 ⟨le_refl t, hrange.2⟩)
  simp only [decide_eq_true_eq] at e1 e2
  simp only [schedule_change, Bool.not_eq_true', decide_eq_false_iff_not, not_not] at hnc
  rw [← e1, ← e2, hnc]

/-- Without schedule changes in `[t1, t2)`, no instant of the interval is a change. -/
theorem no_schedule_changes_implies_constant_schedule {Job : JobType} [DecidableEq Job]
    (sched : schedule (processor_state Job)) (t1 t2 t : instant) :
    (decide (t1 ≤ t) && decide (t < t2)) = true → number_schedule_changes sched t1 t2 = 0 →
    (!schedule_change sched t) = true := by
  intro hrange hzero
  dsimp only [instant] at *
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hrange
  unfold number_schedule_changes at hzero
  rw [List.countP_eq_zero] at hzero
  have := hzero t (mem_index_iota'.2 hrange)
  simpa using this

/-- Without schedule changes strictly within `[t1, t2)`, `scheduled_job` is constant on it. -/
theorem no_changes_implies_same_scheduled_job {Job : JobType} [DecidableEq Job]
    (sched : schedule (processor_state Job)) (t1 t2 t t' : instant) (oj : Option Job) :
    no_schedule_changes_during sched t1 t2 = true →
    (decide (t1 ≤ t) && decide (t < t2)) = true → (decide (t1 ≤ t') && decide (t' < t2)) = true →
    scheduled_job sched t = oj → scheduled_job sched t' = oj := by
  intro hnsc h1 h2 hsc
  dsimp only [instant] at *
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h1 h2
  simp only [no_schedule_changes_during, decide_eq_true_eq, number_schedule_changes,
    List.countP_eq_zero] at hnsc
  -- no change at any instant `s` with `t1 < s < t2`
  have step : ∀ s, t1 < s → s < t2 → scheduled_job sched (s - 1) = scheduled_job sched s := by
    intro s hs1 hs2
    have hmem : s ∈ index_iota (t1 + 1) t2 := mem_index_iota'.2 (show t1 + 1 ≤ s ∧ s < t2 by ((try dsimp only [instant] at *); omega))
    have := hnsc s hmem
    simpa [schedule_change, Nat.pred_eq_sub_one] using this
  -- the scheduled job is constant between any two instants of the interval
  have const : ∀ a d, t1 ≤ a → a + d < t2 → scheduled_job sched (a + d) = scheduled_job sched a := by
    intro a d ha
    induction d with
    | zero => intro _; rfl
    | succ d ih =>
      intro hd
      have hd' : a + d < t2 := by ((try dsimp only [instant] at *); omega)
      rw [← ih hd']
      have := step (a + d + 1) (by ((try dsimp only [instant] at *); omega)) (by ((try dsimp only [instant] at *); omega))
      rw [show a + (d + 1) = a + d + 1 by ((try dsimp only [instant] at *); omega)]
      simpa using this.symm
  rcases le_total t t' with hle | hle
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
    rw [const t d h1.1 h2.2, hsc]
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
    rw [← const t' d h2.1 h1.2, hsc]

end Prosa.Analysis.Facts.Model.Overheads.ScheduleChange
