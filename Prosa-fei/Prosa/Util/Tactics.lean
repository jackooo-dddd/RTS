-- Translated from: ../rt-proofs/util/tactics.v
import Mathlib.Tactic

namespace Prosa.Util.Tactics

def neqP {T : Type _} [DecidableEq T] (x y : T) : Decidable (x ≠ y) := by
  exact instDecidableNot

end Prosa.Util.Tactics
