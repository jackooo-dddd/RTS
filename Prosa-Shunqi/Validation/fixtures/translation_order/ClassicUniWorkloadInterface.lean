import Prosa.Classic.Model.Schedule.Uni.Workload

/-!
Validation-only interface for `classic/model/schedule/uni/workload.v` (classic family): kernel-checked Lean
equations, exported with their proofs and used by the Rocq certificate as propositional equations
(transport) only.
-/

namespace Prosa.Validation.ClassicUniWorkloadInterface

universe u

theorem bigCat_range' {α : Type u} (m n : Nat) (F : Nat → List α) :
    Prosa.Util.Notation.bigCat m n F =
      ((List.range' 0 (n - m)).map (fun i => F (m + i))).flatten := by
  unfold Prosa.Util.Notation.bigCat
  rw [List.range_eq_range']

open Prosa.Util.Sum

theorem production_sumSeq_nil {X : Type u} (F : X → Nat) : sumSeq [] F = 0 := rfl

theorem production_sumSeq_cons {X : Type u} (F : X → Nat) (x : X) (xs : List X) :
    sumSeq (x :: xs) F = F x + sumSeq xs F := by
  simp [sumSeq]

theorem production_sumFiltered_nil {X : Type u} (P : X → Bool) (F : X → Nat) :
    sumFiltered [] P F = 0 := rfl

theorem production_sumFiltered_cons_true {X : Type u} (P : X → Bool) (F : X → Nat)
    (x : X) (xs : List X) (h : P x = true) :
    sumFiltered (x :: xs) P F = F x + sumFiltered xs P F := by
  simp [sumFiltered, h]

theorem production_sumFiltered_cons_false {X : Type u} (P : X → Bool) (F : X → Nat)
    (x : X) (xs : List X) (h : P x = false) :
    sumFiltered (x :: xs) P F = sumFiltered xs P F := by
  simp [sumFiltered, h]

end Prosa.Validation.ClassicUniWorkloadInterface
