-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: util/tactics.v

import Mathlib.Tactic

namespace Prosa.Util.Tactics

universe u

/-- Lean reformulation of MathComp's reflection lemma for disequality.
The Boolean observation remains explicit in the theorem statement. -/
theorem neqP {T : Type u} [DecidableEq T] (x y : T) :
    decide (x ≠ y) = true ↔ x ≠ y := by
  simp

/-- Modus ponens, corresponding directly to the source proposition. -/
theorem modusponens (P Q : Prop) : P → (P → Q) → Q := by
  intro hP hPQ
  exact hPQ hP

end Prosa.Util.Tactics
