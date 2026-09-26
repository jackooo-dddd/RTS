-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/facts/transform/replace_at.v

import Prosa.Analysis.Transform.Swap
import Prosa.Analysis.Facts.Behavior.Service

namespace Prosa.Analysis.Facts.Transform.ReplaceAt

open Prosa.Behavior.Job
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Behavior.Time
open Prosa.Analysis.Transform.Swap
open Prosa.Analysis.Facts.Behavior.Service

/-! Representation notes: a single comparison in `Prop` position is the Lean
proposition; a chained comparison is `(decide _ && decide _) = true`; `~~ b`
is `!b`; `P \/ Q` is `P ∨ Q`; the section-local `Let sched'` is inlined.
Binder orders follow the elaborated types. -/

section ReplaceAtFacts

variable {Job : JobType} [DecidableEq Job] {PState : ProcessorState Job}
variable (sched : schedule PState) (t' : instant) (nstate : PState.State)

/-- The replaced schedule has the new state at `t'`. -/
theorem replace_at_def : replace_at sched t' nstate t' = nstate := by
  simp [replace_at]

/-- The replaced schedule agrees with the original elsewhere. -/
theorem rest_of_schedule_invariant :
    ∀ t : instant, t ≠ t' → replace_at sched t' nstate t = sched t := by
  intro t ht
  have : (t' == t) = false := by simp [Ne.symm ht]
  simp [replace_at, this]

/-- Service in intervals not containing `t'` is unchanged. -/
theorem service_at_other_times_invariant :
    ∀ t1 t2 : Nat, t2 ≤ t' ∨ t' < t1 →
      ∀ j : Job, service_during sched j t1 t2 = service_during (replace_at sched t' nstate) j t1 t2 := by
  intro t1 t2 h j
  unfold service_during
  apply Finset.sum_congr rfl
  intro t ht
  simp only [Finset.mem_Ico] at ht
  have hne : t ≠ t' := by
    try dsimp only [instant] at *
    omega
  unfold service_at
  rw [rest_of_schedule_invariant sched t' nstate t hne]

/-- Service across the replacement point differs exactly by the two states. -/
theorem service_delta :
    ∀ t1 t2 : Nat, (decide (t1 ≤ t') && decide (t' < t2)) = true →
      ∀ j : Job,
        service_during sched j t1 t2 + service_at (replace_at sched t' nstate) j t' =
          service_during (replace_at sched t' nstate) j t1 t2 + service_at sched j t' := by
  intro t1 t2 h j
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  have hmem : t' ∈ Finset.Ico t1 t2 := by
    simp only [Finset.mem_Ico]; exact h
  unfold service_during
  rw [← Finset.add_sum_erase _ _ hmem, ← Finset.add_sum_erase _ _ hmem]
  have hrest : ∑ x ∈ (Finset.Ico t1 t2).erase t', service_at sched j x =
      ∑ x ∈ (Finset.Ico t1 t2).erase t', service_at (replace_at sched t' nstate) j x := by
    apply Finset.sum_congr rfl
    intro x hx
    have hne : x ≠ t' := Finset.ne_of_mem_erase hx
    unfold service_at
    rw [rest_of_schedule_invariant sched t' nstate x hne]
  rw [hrest]
  generalize service_at sched j t' = a
  generalize service_at (replace_at sched t' nstate) j t' = b
  generalize ∑ x ∈ (Finset.Ico t1 t2).erase t', service_at (replace_at sched t' nstate) j x = c
  try dsimp only [work] at *
  omega

/-- The service in an interval containing `t'` after the replacement. -/
theorem service_in_replaced :
    ∀ t1 t2 : Nat, (decide (t1 ≤ t') && decide (t' < t2)) = true →
      ∀ j : Job,
        service_during (replace_at sched t' nstate) j t1 t2 =
          service_during sched j t1 t2 + service_at (replace_at sched t' nstate) j t' -
            service_at sched j t' := by
  intro t1 t2 h j
  have := service_delta sched t' nstate t1 t2 h j
  try dsimp only [work, instant] at *
  omega

/-- A job scheduled in neither state receives the same service at every time. -/
theorem service_at_of_others_invariant (j : Job) :
    (!ProcessorState.scheduled_in PState j (replace_at sched t' nstate t')) = true →
      (!ProcessorState.scheduled_in PState j (sched t')) = true →
        ∀ t : instant, service_at sched j t = service_at (replace_at sched t' nstate) j t := by
  intro h1 h2 t
  by_cases ht : t = t'
  · subst ht
    unfold service_at
    rw [service_in_implies_scheduled_in j _ h2, service_in_implies_scheduled_in j _ h1]
  · unfold service_at
    rw [rest_of_schedule_invariant sched t' nstate t ht]

/-- A job scheduled in neither state receives the same cumulative service. -/
theorem service_during_of_others_invariant (j : Job) :
    (!ProcessorState.scheduled_in PState j (replace_at sched t' nstate t')) = true →
      (!ProcessorState.scheduled_in PState j (sched t')) = true →
        ∀ t1 t2 : instant,
          service_during sched j t1 t2 = service_during (replace_at sched t' nstate) j t1 t2 := by
  intro h1 h2 t1 t2
  unfold service_during
  apply Finset.sum_congr rfl
  intro t _
  exact service_at_of_others_invariant sched t' nstate j h1 h2 t

end ReplaceAtFacts

end Prosa.Analysis.Facts.Transform.ReplaceAt
