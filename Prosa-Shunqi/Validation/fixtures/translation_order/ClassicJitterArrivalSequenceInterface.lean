import Prosa.Classic.Model.Arrival.Jitter.ArrivalSequence

/-!
Validation-only interface for `classic/model/arrival/jitter/arrival_sequence.v` (classic family): kernel-checked Lean
equations, exported with their proofs and used by the Rocq certificate as propositional equations
(transport) only.
-/

namespace Prosa.Validation.ClassicJitterArrivalSequenceInterface

universe u

theorem bigCat_range' {α : Type u} (m n : Nat) (F : Nat → List α) :
    Prosa.Util.Notation.bigCat m n F =
      ((List.range' 0 (n - m)).map (fun i => F (m + i))).flatten := by
  unfold Prosa.Util.Notation.bigCat
  rw [List.range_eq_range']

end Prosa.Validation.ClassicJitterArrivalSequenceInterface
