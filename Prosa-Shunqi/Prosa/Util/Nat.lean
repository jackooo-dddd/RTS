-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: util/nat.v

import Mathlib.Tactic
import Prosa.Util.Tactics

namespace Prosa.Util.Nat

/-- Given `p ≤ m` and `q ≤ n`, distribute truncated subtraction over
addition. -/
theorem subnACA {m n p q : ℕ} :
    p ≤ m → q ≤ n →
      (m + n) - (p + q) = (m - p) + (n - q) := by
  omega

/-- The implication-only form of right subtraction from an inequality. -/
theorem leq_subRL_impl {m n p : ℕ} :
    m + n ≤ p → n ≤ p - m := by
  omega

end Prosa.Util.Nat
