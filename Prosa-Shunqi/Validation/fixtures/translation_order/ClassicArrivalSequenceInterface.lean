import Prosa.Classic.Model.Arrival.Basic.ArrivalSequence

/-!
Validation-only interface for `classic/model/arrival/basic/arrival_sequence.v` (classic family):
a kernel-checked Lean equation, exported with its proof, that reads the accepted v0.6 helper
`Prosa.Util.Notation.bigCat m n F` (the translation of `\cat_(m <= t < n) F t`) as a
concatenation over `List.range' 0 (n - m)`, which the Rocq certificate relates structurally
to MathComp's `iota 0 (n - m)`.  Used as a propositional equation (transport) only.
-/

namespace Prosa.Validation.ClassicArrivalSequenceInterface

universe u

theorem bigCat_range' {α : Type u} (m n : Nat) (F : Nat → List α) :
    Prosa.Util.Notation.bigCat m n F =
      ((List.range' 0 (n - m)).map (fun i => F (m + i))).flatten := by
  unfold Prosa.Util.Notation.bigCat
  rw [List.range_eq_range']

end Prosa.Validation.ClassicArrivalSequenceInterface
