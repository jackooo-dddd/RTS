import Prosa.Util.Div_mod

namespace Prosa.Validation.DivModInterface

open Prosa.Util.Div_mod

/-- Bind the validation interface to the actual production definitions. -/
theorem production_div_floor_eq (x y : Nat) :
    div_floor x y = x / y := rfl

theorem production_div_ceil_eq (x y : Nat) :
    div_ceil x y = if y ∣ x then x / y else x / y + 1 := rfl

/-- Euclidean computation facts for the exact target `Nat.div`/`Nat.mod`. -/
theorem production_div_add_mod (x y : Nat) :
    y * (x / y) + x % y = x := Nat.div_add_mod x y

theorem production_mod_lt (x y : Nat) (hy : 0 < y) :
    x % y < y := Nat.mod_lt x hy

theorem production_div_zero (x : Nat) : x / 0 = 0 := Nat.div_zero x

theorem production_mod_zero (x : Nat) : x % 0 = x := Nat.mod_zero x

theorem production_dvd_iff_mod_eq_zero (x y : Nat) :
    y ∣ x ↔ x % y = 0 := Nat.dvd_iff_mod_eq_zero

end Prosa.Validation.DivModInterface
