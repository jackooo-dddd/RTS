-- Authoritative source:
-- ProsaBuddy classic Prosa (prosabuddy commit f692cb7479780cf6009493f373a309e13165201c)
-- source: classic/implementation/uni/basic/extraction_tdma.v
-- sha256: see Prosa-Shunqi/classic-prosa/comprehensive-classic/file_order.csv (rank 116)

import Prosa.Classic.Analysis.Uni.Basic.TdmaWcrtAnalysis

/-!
A schedulability test for TDMA prepared for extraction. The source file declares no `Module`, so its declarations
live directly in the file namespace.

Representation notes:
* `CoInductive Task_T := build_task : nat -> nat -> nat -> nat -> Task_T` has a single non-recursive constructor;
  it is a Lean `inductive` with the same constructor (Lean has no coinductive data types; for a non-recursive
  constructor the two coincide). Its auto-generated `Task_T_rect/…` eliminators are Lean's `rec`/`casesOn`.
* `x == y` is `decide (x = y)`; `if b then true else false` keeps the source shape with a Boolean condition;
  `foldr plus 0` is `List.foldr (· + ·) 0`.
* The commented-out `Eval`/`Extract` commands of the source declare nothing.
-/

namespace Prosa.Classic.Implementation.Uni.Basic.ExtractionTdma

inductive Task_T : Type where
  | build_task : Nat → Nat → Nat → Nat → Task_T

open Task_T

def get_slot (tsk : Task_T) : Nat :=
  match tsk with
  | build_task x _ _ _ => x

def get_cost (tsk : Task_T) : Nat :=
  match tsk with
  | build_task _ x _ _ => x

def get_D (tsk : Task_T) : Nat :=
  match tsk with
  | build_task _ _ x _ => x

def get_P (tsk : Task_T) : Nat :=
  match tsk with
  | build_task _ _ _ x => x

def task_eq (t1 t2 : Task_T) : Bool :=
  decide (get_slot t1 = get_slot t2) &&
  decide (get_cost t1 = get_cost t2) &&
  decide (get_D t1 = get_D t2) &&
  decide (get_P t1 = get_P t2)

def In (a : Task_T) : List Task_T → Prop
  | [] => False
  | b :: m => a = b ∨ In a m

def schedulable_tsk (T : Nat) (tsk : Task_T) : Bool :=
  let bound := Prosa.Classic.Analysis.Uni.Basic.TdmaWcrtAnalysis.WCRT_OneJobTDMA.WCRT_formula T (get_slot tsk)
    (get_cost tsk)
  if (decide (bound ≤ get_D tsk) && decide (bound ≤ get_P tsk)) then true else false

def schedulability_test (T : Nat) : List Task_T → Bool
  | [] => true
  | x :: s => schedulable_tsk T x && schedulability_test T s

theorem schedulability_test_valid (T : Nat) (TL : List Task_T) :
    schedulability_test T TL = true ↔ (∀ tsk, In tsk TL → schedulable_tsk T tsk = true) := by
  induction TL with
  | nil => simp [schedulability_test, In]
  | cons a TL IH =>
    simp only [schedulability_test, Bool.and_eq_true, In]
    constructor
    · rintro ⟨H1, H2⟩ tsk (EQ | IN)
      · subst EQ; exact H1
      · exact IH.mp H2 tsk IN
    · intro ALL
      exact ⟨ALL a (Or.inl rfl), IH.mpr (fun tsk IN => ALL tsk (Or.inr IN))⟩

def cycle (l : List Task_T) : Nat :=
  List.foldr (· + ·) 0 (l.map get_slot)

def schedulability_tdma (l : List Task_T) : Bool :=
  schedulability_test (cycle l) l

theorem schedulability_tdma_valid (task_list : List Task_T) :
    schedulability_tdma task_list = true ↔
      (∀ tsk, In tsk task_list → schedulable_tsk (cycle task_list) tsk = true) :=
  schedulability_test_valid (cycle task_list) task_list

end Prosa.Classic.Implementation.Uni.Basic.ExtractionTdma
