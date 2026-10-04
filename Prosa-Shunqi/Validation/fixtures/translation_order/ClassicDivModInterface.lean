import Prosa.Classic.Util.DivMod

/-!
Validation-only interface for `classic/util/div_mod.v` (classic family).  These kernel-checked
Lean equations use the same names as the accepted v0.6 `DivModComputationInterface`, so that its
audited operation-level correspondence (`certificates/common/DivModCorrespondence.v`) is
instantiated for this exact imported artifact by re-binding only: the production definitions
are the classic `div_floor`/`div_ceil` (the same bodies as v0.6 `util/div_mod.v`), and the
Euclidean facts characterize the target `Nat.div`/`Nat.mod`.
-/

namespace Prosa.Validation.DivModInterface

open Prosa.Classic.Util.DivMod

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
