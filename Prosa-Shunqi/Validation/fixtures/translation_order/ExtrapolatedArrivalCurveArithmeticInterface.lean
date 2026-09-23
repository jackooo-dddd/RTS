import Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve

namespace Prosa.Validation.ExtrapolatedArrivalCurveArithmeticInterface

/-- Validation-only Euclidean laws for the exact `Nat.div`/`Nat.mod`
    operations used by the compiled production module.  Their proof bodies
    are exported and kernel-checked, never statement-only assumptions. -/
theorem production_div_add_mod (x y : Nat) :
    y * (x / y) + x % y = x := Nat.div_add_mod x y

theorem production_mod_lt (x y : Nat) (hy : 0 < y) :
    x % y < y := Nat.mod_lt x hy

theorem production_div_zero (x : Nat) : x / 0 = 0 := Nat.div_zero x

theorem production_mod_zero (x : Nat) : x % 0 = x := Nat.mod_zero x

#print axioms production_div_add_mod
#print axioms production_mod_lt
#print axioms production_div_zero
#print axioms production_mod_zero

end Prosa.Validation.ExtrapolatedArrivalCurveArithmeticInterface
