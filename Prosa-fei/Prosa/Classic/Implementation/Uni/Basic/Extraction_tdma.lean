-- Translated from: ../rt-proofs/classic/implementation/uni/basic/extraction_tdma.v
import Prosa.Classic.Analysis.Uni.Basic.Tdma_wcrt_analysis
import Mathlib.Tactic

namespace Prosa.Classic.Implementation.Uni.Basic.Extraction_tdma

open Prosa.Classic.Analysis.Uni.Basic.Tdma_wcrt_analysis

structure Task_T where
  slot : ℕ
  cost : ℕ
  D : ℕ
  P : ℕ

def get_slot (tsk : Task_T) : ℕ := tsk.slot

def get_cost (tsk : Task_T) : ℕ := tsk.cost

def get_D (tsk : Task_T) : ℕ := tsk.D

def get_P (tsk : Task_T) : ℕ := tsk.P

def task_eq (t1 t2 : Task_T) : Bool :=
  (get_slot t1 == get_slot t2) &&
  (get_cost t1 == get_cost t2) &&
  (get_D t1 == get_D t2) &&
  (get_P t1 == get_P t2)

def In (a : Task_T) : List Task_T → Prop
  | [] => False
  | b :: m => a = b ∨ In a m

noncomputable def schedulable_tsk (T : ℕ) (tsk : Task_T) : Bool :=
  let bound := WCRT_formula_fn T (get_slot tsk) (get_cost tsk)
  if (decide (bound ≤ get_D tsk)) && (decide (bound ≤ get_P tsk)) then true else false

noncomputable def schedulability_test (T : ℕ) : List Task_T → Bool
  | [] => true
  | x :: s => schedulable_tsk T x && schedulability_test T s

theorem schedulability_test_valid (T : ℕ) (TL : List Task_T) :
    schedulability_test T TL = true ↔
      (∀ tsk, In tsk TL → schedulable_tsk T tsk = true) := by
  induction TL with
  | nil =>
    refine ⟨fun _ tsk h => absurd h id, fun _ => rfl⟩
  | cons x s ih =>
    refine ⟨fun h tsk hin => ?_, fun hall => ?_⟩
    · have hx := (Bool.and_eq_true_iff.mp h).1
      have hs := (Bool.and_eq_true_iff.mp h).2
      exact hin.elim (fun heq => heq ▸ hx) (fun hin => ih.mp hs tsk hin)
    · exact Bool.and_eq_true_iff.mpr ⟨hall x (Or.inl rfl),
        ih.mpr (fun tsk hin => hall tsk (Or.inr hin))⟩

def cycle (l : List Task_T) : ℕ :=
  (l.map get_slot).foldr (· + ·) 0

noncomputable def schedulability_tdma (l : List Task_T) : Bool :=
  schedulability_test (cycle l) l

theorem schedulability_tdma_valid (task_list : List Task_T) :
    schedulability_tdma task_list = true ↔
      (∀ tsk, In tsk task_list → schedulable_tsk (cycle task_list) tsk = true) := by
  exact schedulability_test_valid (cycle task_list) task_list

end Prosa.Classic.Implementation.Uni.Basic.Extraction_tdma
