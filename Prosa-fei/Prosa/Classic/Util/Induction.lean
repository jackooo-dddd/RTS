-- Translated from: ../rt-proofs/classic/util/induction.v
import Mathlib.Tactic
import Prosa.Classic.Util.Tactics

namespace Prosa.Classic.Util.Induction

section NatInduction

lemma strong_ind (P : Nat → Prop)
    (h : ∀ n, (∀ k, k < n → P k) → P n) :
    ∀ n, P n := by
  intro n
  exact Nat.strongRecOn n (fun k ih => h k ih)

lemma leq_as_delta (x1 : Nat) (P : Nat → Prop) :
    (∀ x2, x1 ≤ x2 → P x2) ↔ (∀ delta, P (x1 + delta)) := by
  constructor
  · intro h delta
    apply h
    omega
  · intro h x2 hle
    have := h (x2 - x1)
    rwa [Nat.add_sub_cancel' hle] at this

end NatInduction

end Prosa.Classic.Util.Induction
