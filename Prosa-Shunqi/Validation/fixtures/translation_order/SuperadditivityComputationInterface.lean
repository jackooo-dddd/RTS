import Prosa.Util.Superadditivity

/-! Kernel-checked computation observations of the current compiled
production snapshot. These are validation-only and add no theorem premise. -/

namespace Prosa.Validation.SuperadditivityInterface

theorem productionMinimal (f : Nat → Nat) (h : Nat) :
    Prosa.Util.Superadditivity.minimal_superadditive_extension f h =
      Prosa.Util.List.max0
        ((Prosa.Util.List.index_iota 1 h).map
          (fun a => f a + f (h - a))) := by rfl

theorem productionIndexIota (a b : Nat) :
    Prosa.Util.List.index_iota a b = List.range' a (b - a) := by rfl

theorem productionMax0 (xs : List Nat) :
    Prosa.Util.List.max0 xs = xs.foldl Nat.max 0 := by rfl

theorem rangeZero (a : Nat) : List.range' a 0 = [] := by rfl
theorem rangeSucc (a n : Nat) :
    List.range' a (Nat.succ n) = a :: List.range' (a + 1) n := by rfl

theorem mapNil (f : Nat → Nat) : List.map f [] = [] := by rfl
theorem mapCons (f : Nat → Nat) (a : Nat) (xs : List Nat) :
    List.map f (a :: xs) = f a :: List.map f xs := by rfl

theorem foldlNil (z : Nat) :
    List.foldl Nat.max z [] = z := by rfl
theorem foldlCons (z a : Nat) (xs : List Nat) :
    List.foldl Nat.max z (a :: xs) =
      List.foldl Nat.max (Nat.max z a) xs := by rfl

/-- Definitionally the update expression in the two compiled horizon theorem
types. The exact-type guards in Rocq confirm this connection after import. -/
def updateValue (f : Nat → Nat) (h t : Nat) : Nat :=
  if decide (t = h) then
    Prosa.Util.Superadditivity.minimal_superadditive_extension f h
  else f t

theorem updateValueEq (f : Nat → Nat) (h : Nat) :
    updateValue f h h =
      Prosa.Util.Superadditivity.minimal_superadditive_extension f h := by
  unfold updateValue
  rw [decide_eq_true (rfl : h = h)]
  rfl

theorem updateValueNe (f : Nat → Nat) (h t : Nat) (hne : t ≠ h) :
    updateValue f h t = f t := by
  unfold updateValue
  rw [decide_eq_false hne]
  rfl

end Prosa.Validation.SuperadditivityInterface
