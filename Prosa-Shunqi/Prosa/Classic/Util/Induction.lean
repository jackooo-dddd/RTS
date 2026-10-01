-- Authoritative source:
-- ProsaBuddy classic Prosa (prosabuddy commit f692cb7479780cf6009493f373a309e13165201c)
-- source: classic/util/induction.v
-- sha256: see Prosa-Shunqi/classic-prosa/casestudy-translation/file_order.csv (rank 8)

/-! Induction lemmas for natural numbers. -/

namespace Prosa.Classic.Util.Induction

theorem strong_ind :
    ∀ (P : Nat → Prop),
      (∀ n, (∀ k, k < n → P k) → P n) →
      ∀ n, P n := by
  intro P ALL n
  exact Nat.strongRecOn n ALL

theorem leq_as_delta :
    ∀ (x1 : Nat) (P : Nat → Prop),
      (∀ x2, x1 ≤ x2 → P x2) ↔
      (∀ delta, P (x1 + delta)) := by
  intro x1 P
  constructor
  · intro ALL delta
    exact ALL (x1 + delta) (Nat.le_add_right x1 delta)
  · intro ALL x2 LE
    have h := ALL (x2 - x1)
    rwa [Nat.add_sub_cancel' LE] at h

end Prosa.Classic.Util.Induction
