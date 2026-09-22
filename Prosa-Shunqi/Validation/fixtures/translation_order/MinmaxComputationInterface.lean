import Prosa.Util.Minmax

namespace Prosa.Validation.MinmaxInterface

universe u

open Prosa.Util.Minmax

/-- Actual-artifact equations for the ordered conditional maximum. -/
theorem production_bigMaxListCond_nil {X : Type u} (P : X → Bool)
    (F : X → Nat) : bigMaxListCond [] P F = 0 := rfl

theorem production_bigMaxListCond_cons {X : Type u} (x : X) (xs : List X)
    (P : X → Bool) (F : X → Nat) :
    bigMaxListCond (x :: xs) P F =
      if P x then Nat.max (F x) (bigMaxListCond xs P F)
      else bigMaxListCond xs P F := rfl

/-- Actual-artifact equations for the canonical half-open natural range. -/
theorem production_bigMaxNatRange_zero (P : Nat → Bool) :
    bigMaxNatRange 0 P = 0 := rfl

theorem production_bigMaxNatRange_succ (n : Nat) (P : Nat → Bool) :
    bigMaxNatRange (n + 1) P =
      if P n then Nat.max (bigMaxNatRange n P) n
      else bigMaxNatRange n P := rfl

/-- Constructor equations for the Boolean existential used by witness facts. -/
theorem production_any_nil {X : Type u} (P : X → Bool) :
    List.any ([] : List X) P = false := rfl

theorem production_any_cons {X : Type u} (x : X) (xs : List X)
    (P : X → Bool) :
    List.any (x :: xs) P = (P x || xs.any P) := rfl

/-- Recursor equations sufficient for a representation-independent Nat.max bridge. -/
theorem production_natMax_zero_left (n : Nat) : Nat.max 0 n = n := rfl

theorem production_natMax_zero_right (n : Nat) : Nat.max n 0 = n := by
  exact Nat.max_zero n

theorem production_natMax_succ_succ (m n : Nat) :
    Nat.max (Nat.succ m) (Nat.succ n) = Nat.succ (Nat.max m n) := by
  exact Nat.succ_max_succ m n

end Prosa.Validation.MinmaxInterface
