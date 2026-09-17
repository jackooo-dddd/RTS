-- Translated from: ../rt-proofs/analysis/facts/transform/replace_at.v
import Prosa.Analysis.Transform.Swap
import Prosa.Analysis.Facts.Behavior.Completion

namespace Prosa.Analysis.Facts.Transform.Replace_at

open Prosa.Behavior.Time
open Prosa.Behavior.Job
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Analysis.Transform.Swap
open Prosa.Analysis.Facts.Behavior.Service

section ReplaceAtFacts

variable {Job : JobType}
variable {PState : Type _} [DecidableEq PState]
variable [ProcessorState Job PState]
variable (sched : schedule PState)
variable (t' : instant)
variable (nstate : PState)

noncomputable def sched' : schedule PState := replace_at sched t' nstate

theorem rest_of_schedule_invariant :
    ∀ t, t ≠ t' → sched' sched t' nstate t = sched t := by
  intro t DIFF
  unfold sched' replace_at
  have hne : ¬ (t' == t) = true := by
    rw [beq_iff_eq]
    exact Ne.symm DIFF
  simp [hne]

theorem service_at_other_times_invariant :
    ∀ t1 t2,
      t2 ≤ t' ∨ t' < t1 →
      ∀ (j : Job),
        service_during sched j t1 t2 =
        service_during (sched' sched t' nstate) j t1 t2 := by
  intro t1 t2 SWAP_EXCLUDED j
  simp only [service_during, service_at]
  apply Finset.sum_congr rfl
  intro t ht
  rw [Finset.mem_Ico] at ht
  have hne : t ≠ t' := Prosa.Util.Nat.point_not_in_interval t1 t2 t' SWAP_EXCLUDED t ⟨ht.1, ht.2⟩
  rw [rest_of_schedule_invariant sched t' nstate t hne]

theorem service_delta :
    ∀ t1 t2,
      t1 ≤ t' ∧ t' < t2 →
      ∀ (j : Job),
        service_during sched j t1 t2 + service_at (sched' sched t' nstate) j t' =
        service_during (sched' sched t' nstate) j t1 t2 + service_at sched j t' := by
  intro t1 t2 ⟨h1, h2⟩ j
  -- Split both service_during at point t'
  rw [← service_split_at_point sched j t1 t' t2 ⟨h1, h2⟩,
      ← service_split_at_point (sched' sched t' nstate) j t1 t' t2 ⟨h1, h2⟩]
  -- The parts before t' and after t'+1 are invariant
  rw [← service_at_other_times_invariant sched t' nstate t1 t' (Or.inl (le_refl _)) j,
      ← service_at_other_times_invariant sched t' nstate (t' + 1) t2 (Or.inr (Nat.lt_succ_of_le (le_refl _))) j]
  -- Now both sides should have the same terms, just rearranged
  ring

theorem service_in_replaced :
    ∀ t1 t2,
      t1 ≤ t' ∧ t' < t2 →
      ∀ (j : Job),
        service_during (sched' sched t' nstate) j t1 t2 =
        service_during sched j t1 t2 + service_at (sched' sched t' nstate) j t' - service_at sched j t' := by
  intro t1 t2 ORDER j
  have h := service_delta sched t' nstate t1 t2 ORDER j
  -- h : SD + SA' = SD' + SA
  -- goal : SD' = SD + SA' - SA
  -- i.e., SD' = (SD + SA') - SA, which follows from h since SD' + SA = SD + SA'
  -- Use Tsub.tsub characterization
  apply Nat.eq_sub_of_add_eq
  rw [Nat.add_comm]
  rw [show service_at sched j t' + service_during (sched' sched t' nstate) j t1 t2 =
      service_during (sched' sched t' nstate) j t1 t2 + service_at sched j t' from Nat.add_comm _ _]
  exact h.symm

theorem service_at_of_others_invariant (j : Job) :
    ¬ ProcessorState.scheduled_in j (sched' sched t' nstate t') = true →
    ¬ ProcessorState.scheduled_in j (sched t') = true →
    ∀ t,
      service_at sched j t = service_at (sched' sched t' nstate) j t := by
  intro NOT_IN_NEW NOT_IN_OLD t
  by_cases TT : t = t'
  · simp only [service_at]
    rw [TT]
    have h1 : ProcessorState.service_in j (sched t') = 0 := by
      apply ProcessorState.service_implies_scheduled
      simp only [ProcessorState.scheduled_in, decide_eq_true_eq] at NOT_IN_OLD
      exact NOT_IN_OLD
    have h2 : ProcessorState.service_in j (sched' sched t' nstate t') = 0 := by
      apply ProcessorState.service_implies_scheduled
      simp only [ProcessorState.scheduled_in, decide_eq_true_eq] at NOT_IN_NEW
      exact NOT_IN_NEW
    rw [h1, h2]
  · simp only [service_at]
    rw [rest_of_schedule_invariant sched t' nstate t TT]

theorem service_during_of_others_invariant (j : Job) :
    ¬ ProcessorState.scheduled_in j (sched' sched t' nstate t') = true →
    ¬ ProcessorState.scheduled_in j (sched t') = true →
    ∀ t1 t2,
      service_during sched j t1 t2 = service_during (sched' sched t' nstate) j t1 t2 := by
  intro NOT_IN_NEW NOT_IN_OLD t1 t2
  simp only [service_during]
  apply Finset.sum_congr rfl
  intro t _
  exact service_at_of_others_invariant sched t' nstate j NOT_IN_NEW NOT_IN_OLD t

end ReplaceAtFacts

end Prosa.Analysis.Facts.Transform.Replace_at
