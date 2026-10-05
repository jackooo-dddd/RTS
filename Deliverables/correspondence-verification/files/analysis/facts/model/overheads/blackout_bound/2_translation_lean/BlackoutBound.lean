-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/facts/model/overheads/blackout_bound.v

import Prosa.Model.Processor.OverheadResourceModel
import Prosa.Analysis.Facts.Behavior.Supply

namespace Prosa.Analysis.Facts.Model.Overheads.BlackoutBound

open Prosa.Behavior.Job
open Prosa.Behavior.Schedule
open Prosa.Behavior.Time
open Prosa.Model.Processor.Supply
open Prosa.Model.Processor.Overheads
open Prosa.Model.Processor.OverheadResourceModel
open Prosa.Analysis.Definitions.Overheads.ScheduleChange
open Prosa.Analysis.Facts.Model.Overheads.Schedule
open Prosa.Analysis.Facts.Model.Overheads.ScheduleChange
open Prosa.Analysis.Facts.Behavior.Supply
open Prosa.Util.List

/-! A bound on the total blackout time (time without supply, i.e. spent in overheads) of an explicit-overhead
schedule, given the number of schedule changes. Binders follow the elaborated source types (the unused section
hypotheses are not part of the statements). Representation: a Boolean in `Prop` position is `= true`; `t1.+1`
is `t1 + 1`. -/

variable {Job : JobType} [DecidableEq Job]

/-- LEAN_HELPER: membership in `index_iota`. -/
private theorem bb_mem_index_iota {a b t : Nat} : t ∈ index_iota a b ↔ a ≤ t ∧ t < b := by
  simp only [index_iota, List.mem_range']
  constructor
  · rintro ⟨i, hi, rfl⟩; omega
  · rintro ⟨h1, h2⟩; exact ⟨t - a, by omega, by omega⟩

/-- LEAN_HELPER: an interval sum over an empty interval vanishes. -/
private theorem bb_blackout_empty (sched : schedule (processor_state Job)) {t1 t2 : instant} (h : t2 ≤ t1) :
    blackout_during sched t1 t2 = 0 := by
  simp [blackout_during, Finset.Ico_eq_empty_of_le h]

/-- LEAN_HELPER: without schedule changes strictly inside `[t1, t2)`, the job scheduled at `t1` is scheduled
throughout the interval. -/
private theorem bb_same_job (sched : schedule (processor_state Job)) {t1 t2 t : instant}
    (hnsc : no_schedule_changes_during sched t1 t2 = true) (h1 : t1 ≤ t) (h2 : t < t2) :
    scheduled_job sched t = scheduled_job sched t1 :=
  no_changes_implies_same_scheduled_job sched t1 t2 t1 t (scheduled_job sched t1) hnsc
    (by simp only [Bool.and_eq_true, decide_eq_true_eq]; exact ⟨le_refl _, by ((try dsimp only [instant] at *); omega)⟩)
    (by simp only [Bool.and_eq_true, decide_eq_true_eq]; exact ⟨h1, h2⟩) rfl

/-- LEAN_HELPER: without schedule changes, the job scheduled at `t1` is invariant over `[t1, t2)`. -/
private theorem bb_invariant (sched : schedule (processor_state Job)) {t1 t2 : instant}
    (hnsc : no_schedule_changes_during sched t1 t2 = true) :
    scheduled_job_invariant sched (scheduled_job sched t1) t1 t2 = true := by
  unfold scheduled_job_invariant
  rw [List.all_eq_true]
  intro t ht
  have ht' := bb_mem_index_iota.1 ht
  simp [bb_same_job sched hnsc ht'.1 ht'.2]

/-- LEAN_HELPER: the pointwise filter by the job scheduled at `t1` is the identity on `[t1, t2)`. -/
private theorem bb_filter_eq (sched : schedule (processor_state Job)) {t1 t2 : instant}
    (hnsc : no_schedule_changes_during sched t1 t2 = true) (f : instant → Bool) :
    ∑ t ∈ Finset.Ico t1 t2, (f t).toNat =
      ∑ t ∈ Finset.Ico t1 t2, (decide (scheduled_job sched t = scheduled_job sched t1) && f t).toNat := by
  apply Finset.sum_congr rfl
  intro t ht
  rw [Finset.mem_Ico] at ht
  simp [bb_same_job sched hnsc ht.1 ht.2]

/-- The total blackout duration in `[t1, t2)` decomposes into dispatch, context-switch and CRPD time. -/
theorem blackout_during_split (sched : schedule (processor_state Job)) (t1 t2 : instant) :
    blackout_during sched t1 t2 =
      total_time_in_dispatch sched t1 t2 + total_time_in_context_switch sched t1 t2 +
        total_time_in_CRPD sched t1 t2 := by
  unfold blackout_during total_time_in_dispatch total_time_in_context_switch total_time_in_CRPD
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t _
  have hs : supply_at sched t = overheads_supply_on (sched t) () := rfl
  simp only [is_blackout, has_supply, hs, is_dispatch, is_context_switch, is_CRPD]
  cases sched t <;> simp [overheads_supply_on]

/-- Without schedule changes, the total dispatch time equals the dispatch time of one job (or idle). -/
theorem total_dispatch_time_eq_job_dispatch_time (sched : schedule (processor_state Job)) (t1 t2 : instant) :
    no_schedule_changes_during sched t1 t2 = true →
    ∃ oj : Option Job, total_time_in_dispatch sched t1 t2 = time_spent_in_dispatch sched oj t1 t2 :=
  fun hnsc => ⟨scheduled_job sched t1, bb_filter_eq sched hnsc _⟩

/-- Without schedule changes, the total context-switch time equals that of one job (or idle). -/
theorem total_cswitch_time_eq_job_cswitch_time (sched : schedule (processor_state Job)) (t1 t2 : instant) :
    no_schedule_changes_during sched t1 t2 = true →
    ∃ oj : Option Job, total_time_in_context_switch sched t1 t2 = time_spent_in_context_switch sched oj t1 t2 :=
  fun hnsc => ⟨scheduled_job sched t1, bb_filter_eq sched hnsc _⟩

/-- Without schedule changes, the total CRPD time equals that of one job (or idle). -/
theorem total_CRPD_time_eq_job_CRPD_time (sched : schedule (processor_state Job)) (t1 t2 : instant) :
    no_schedule_changes_during sched t1 t2 = true →
    ∃ oj : Option Job, total_time_in_CRPD sched t1 t2 = time_spent_in_CRPD sched oj t1 t2 :=
  fun hnsc => ⟨scheduled_job sched t1, bb_filter_eq sched hnsc _⟩

/-- Without schedule changes, the total dispatch time is at most `DB`. -/
theorem total_time_in_dispatch_is_bounded (sched : schedule (processor_state Job)) (DB CSB CRPDB : duration) :
    overhead_resource_model sched DB CSB CRPDB →
    ∀ t1 t2 : instant, no_schedule_changes_during sched t1 t2 = true → total_time_in_dispatch sched t1 t2 ≤ DB := by
  intro horm t1 t2 hnsc
  have heq : total_time_in_dispatch sched t1 t2 = time_spent_in_dispatch sched (scheduled_job sched t1) t1 t2 :=
    bb_filter_eq sched hnsc _
  rw [heq]
  exact horm.1 t1 t2 _ (bb_invariant sched hnsc)

/-- Without schedule changes, the total context-switch time is at most `CSB`. -/
theorem total_time_in_cswitch_is_bounded (sched : schedule (processor_state Job)) (DB CSB CRPDB : duration) :
    overhead_resource_model sched DB CSB CRPDB →
    ∀ t1 t2 : instant, no_schedule_changes_during sched t1 t2 = true →
      total_time_in_context_switch sched t1 t2 ≤ CSB := by
  intro horm t1 t2 hnsc
  have heq : total_time_in_context_switch sched t1 t2 =
      time_spent_in_context_switch sched (scheduled_job sched t1) t1 t2 := bb_filter_eq sched hnsc _
  rw [heq]
  exact horm.2.1 t1 t2 _ (bb_invariant sched hnsc)

/-- Without schedule changes, the total CRPD time is at most `CRPDB`. -/
theorem total_time_in_CRPD_is_bounded (sched : schedule (processor_state Job)) (DB CSB CRPDB : duration) :
    overhead_resource_model sched DB CSB CRPDB →
    ∀ t1 t2 : instant, no_schedule_changes_during sched t1 t2 = true → total_time_in_CRPD sched t1 t2 ≤ CRPDB := by
  intro horm t1 t2 hnsc
  have heq : total_time_in_CRPD sched t1 t2 = time_spent_in_CRPD sched (scheduled_job sched t1) t1 t2 :=
    bb_filter_eq sched hnsc _
  rw [heq]
  exact horm.2.2.1 t1 t2 _ (bb_invariant sched hnsc)

/-- Without schedule changes in `(t1, t2)`, the blackout in `[t1, t2)` is at most `DB + CSB + CRPDB`. -/
theorem no_sched_changes_bounded_overheads_blackout (sched : schedule (processor_state Job))
    (DB CSB CRPDB : duration) :
    overhead_resource_model sched DB CSB CRPDB →
    ∀ t1 t2 : instant, no_schedule_changes_during sched t1 t2 = true →
      blackout_during sched t1 t2 ≤ DB + CSB + CRPDB := by
  intro horm t1 t2 hnsc
  rw [blackout_during_split]
  have h1 := total_time_in_dispatch_is_bounded sched DB CSB CRPDB horm t1 t2 hnsc
  have h2 := total_time_in_cswitch_is_bounded sched DB CSB CRPDB horm t1 t2 hnsc
  have h3 := total_time_in_CRPD_is_bounded sched DB CSB CRPDB horm t1 t2 hnsc
  omega

/-- LEAN_HELPER: the number of schedule changes in `[t1, t1 + 1)` when `t1` is a change. -/
private theorem bb_count_single (sched : schedule (processor_state Job)) {t1 : instant}
    (hsc : schedule_change sched t1 = true) : number_schedule_changes sched t1 (t1 + 1) = 1 := by
  unfold number_schedule_changes
  have : index_iota t1 (t1 + 1) = [t1] := by simp [index_iota]
  rw [this]
  simp [hsc]

/-- LEAN_HELPER: splitting off the first instant of the count. -/
private theorem bb_count_split (sched : schedule (processor_state Job)) (t1 t2 : instant) (hlt : t1 < t2)
    (hsc : schedule_change sched t1 = true) :
    number_schedule_changes sched t1 t2 = 1 + number_schedule_changes sched (t1 + 1) t2 := by
  have hc := number_schedule_changes_cat sched (t1 + 1) t1 t2
    (by simp only [Bool.and_eq_true, decide_eq_true_eq]; exact ⟨by ((try dsimp only [instant] at *); omega), by ((try dsimp only [instant] at *); omega)⟩)
  rw [hc, bb_count_single sched hsc]

/-- With exactly one schedule change in `[t1, t2)`, at `t1`, the blackout is at most `DB + CSB + CRPDB`. -/
theorem sched_changes_start_busy_pref_bounded_overheads_blackout (sched : schedule (processor_state Job))
    (DB CSB CRPDB : duration) :
    overhead_resource_model sched DB CSB CRPDB →
    ∀ t1 t2 : instant, number_schedule_changes sched t1 t2 = 1 → schedule_change sched t1 = true →
      blackout_during sched t1 t2 ≤ DB + CSB + CRPDB := by
  intro horm t1 t2 hnum hsc
  by_cases hle : t2 ≤ t1
  · rw [bb_blackout_empty sched hle]; exact Nat.zero_le _
  · apply no_sched_changes_bounded_overheads_blackout sched DB CSB CRPDB horm
    have := bb_count_split sched t1 t2 (by ((try dsimp only [instant] at *); omega)) hsc
    unfold no_schedule_changes_during
    simp only [decide_eq_true_eq]
    ((try dsimp only [instant] at *); omega)

/-- With exactly `k` schedule changes in `[t1, t2)`, one of them at `t1`, the blackout is at most
`(DB + CSB + CRPDB) * k`. -/
theorem fin_sched_changes_start_busy_pref_bounded_overheads_blackout (sched : schedule (processor_state Job))
    (DB CSB CRPDB : duration) :
    overhead_resource_model sched DB CSB CRPDB →
    ∀ (k : Nat) (t1 t2 : instant), schedule_change sched t1 = true → number_schedule_changes sched t1 t2 = k →
      blackout_during sched t1 t2 ≤ (DB + CSB + CRPDB) * k := by
  intro horm k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro t1 t2 hsc hnum
    by_cases hle : t2 ≤ t1
    · rw [bb_blackout_empty sched hle]; exact Nat.zero_le _
    · have hsplit := bb_count_split sched t1 t2 (by ((try dsimp only [instant] at *); omega)) hsc
      by_cases hz : number_schedule_changes sched (t1 + 1) t2 = 0
      · have h1 : number_schedule_changes sched t1 t2 = 1 := by ((try dsimp only [instant] at *); omega)
        have hb := sched_changes_start_busy_pref_bounded_overheads_blackout sched DB CSB CRPDB horm t1 t2 h1 hsc
        have hk : k = 1 := by ((try dsimp only [instant] at *); omega)
        rw [hk, Nat.mul_one]; exact hb
      · obtain ⟨t, ht, hsct, hn1, hn2⟩ := first_schedule_change_exists sched (t1 + 1) t2
          (number_schedule_changes sched (t1 + 1) t2) (Nat.pos_of_ne_zero hz) rfl
        simp only [Bool.and_eq_true, decide_eq_true_eq] at ht
        have hcat := blackout_during_cat sched t1 t2 t ⟨by ((try dsimp only [instant] at *); omega), by ((try dsimp only [instant] at *); omega)⟩
        have hleft : blackout_during sched t1 t ≤ DB + CSB + CRPDB := by
          apply sched_changes_start_busy_pref_bounded_overheads_blackout sched DB CSB CRPDB horm t1 t _ hsc
          rw [bb_count_split sched t1 t (by ((try dsimp only [instant] at *); omega)) hsc, hn1]
        have hright := ih (number_schedule_changes sched (t1 + 1) t2) (by ((try dsimp only [instant] at *); omega)) t t2 hsct hn2
        have hk : k = number_schedule_changes sched (t1 + 1) t2 + 1 := by ((try dsimp only [instant] at *); omega)
        rw [hk, Nat.mul_succ]
        generalize (DB + CSB + CRPDB) * number_schedule_changes sched (t1 + 1) t2 = P at hright ⊢
        ((try dsimp only [instant] at *); omega)

/-- With exactly `k` schedule changes in `[t1 + 1, t2)`, the blackout in `[t1, t2)` is at most
`(DB + CSB + CRPDB) * (k + 1)`. -/
theorem finite_sched_changes_bounded_overheads_blackout (sched : schedule (processor_state Job))
    (DB CSB CRPDB : duration) :
    overhead_resource_model sched DB CSB CRPDB →
    ∀ (k : Nat) (t1 t2 : instant), number_schedule_changes sched (t1 + 1) t2 = k →
      blackout_during sched t1 t2 ≤ (DB + CSB + CRPDB) * (k + 1) := by
  intro horm k t1 t2 hnum
  by_cases hz : k = 0
  · subst hz
    rw [Nat.zero_add, Nat.mul_one]
    apply no_sched_changes_bounded_overheads_blackout sched DB CSB CRPDB horm
    unfold no_schedule_changes_during
    simp [hnum]
  · obtain ⟨t, ht, hsct, hn1, hn2⟩ := first_schedule_change_exists sched (t1 + 1) t2 k (Nat.pos_of_ne_zero hz) hnum
    simp only [Bool.and_eq_true, decide_eq_true_eq] at ht
    have hcat := blackout_during_cat sched t1 t2 t ⟨by ((try dsimp only [instant] at *); omega), by ((try dsimp only [instant] at *); omega)⟩
    have hleft : blackout_during sched t1 t ≤ DB + CSB + CRPDB := by
      apply no_sched_changes_bounded_overheads_blackout sched DB CSB CRPDB horm
      unfold no_schedule_changes_during
      simp [hn1]
    have hright := fin_sched_changes_start_busy_pref_bounded_overheads_blackout sched DB CSB CRPDB horm k t t2
      hsct hn2
    rw [Nat.mul_succ]
    generalize (DB + CSB + CRPDB) * k = P at hright ⊢
    ((try dsimp only [instant] at *); omega)

end Prosa.Analysis.Facts.Model.Overheads.BlackoutBound
