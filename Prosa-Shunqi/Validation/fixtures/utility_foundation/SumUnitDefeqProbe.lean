import Prosa.Util.Sum

open scoped BigOperators

example (F : Unit → Nat) : (∑ r : Unit, F r) = F () := by
  rfl
