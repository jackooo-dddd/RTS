import Prosa.Analysis.Definitions.RequestBoundFunction
import Validation.fixtures.translation_order.PreemptionParameterComputationInterface

/-!
Export root for `analysis/definitions/request_bound_function.v`: the
production declarations, the accepted preemption-parameter export root, and
kernel-checked constructor equations for `sumSeq` and `sumFiltered`.  Every
equation is proved in Lean and exported with its proof.
-/

namespace Prosa.Validation.RequestBoundFunctionInterface

open Prosa.Util.Sum

universe u

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

end Prosa.Validation.RequestBoundFunctionInterface
