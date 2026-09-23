import Prosa.Util.Lcmseq

namespace Prosa.Validation.LcmseqInterface

open Prosa.Util.Lcmseq

/-- Source-shaped projection of the actual compiled production definition. -/
def lcmlProjection (xs : List Nat) : Nat :=
  xs.foldr Nat.lcm 1

theorem lcmlProjection_guard :
    @Prosa.Util.Lcmseq.lcml = @lcmlProjection := rfl

/-- Computation equations for the exact core arithmetic used by `Nat.lcm`. -/
theorem production_gcd_def (x y : Nat) :
    Nat.gcd x y = if x = 0 then y else Nat.gcd (y % x) x :=
  Nat.gcd_def x y

theorem production_lcm_eq_mul_div (x y : Nat) :
    Nat.lcm x y = x * y / Nat.gcd x y := rfl

end Prosa.Validation.LcmseqInterface

/-!
These operation facts intentionally use the same names as the already audited
Div/Mod interface so that its correspondence proof can be instantiated for
this exact imported artifact without copying that proof.
-/
namespace Prosa.Validation.DivModInterface

theorem production_div_add_mod (x y : Nat) :
    y * (x / y) + x % y = x := Nat.div_add_mod x y

theorem production_mod_lt (x y : Nat) (hy : 0 < y) :
    x % y < y := Nat.mod_lt x hy

theorem production_div_zero (x : Nat) : x / 0 = 0 := Nat.div_zero x

theorem production_mod_zero (x : Nat) : x % 0 = x := Nat.mod_zero x

theorem production_dvd_iff_mod_eq_zero (x y : Nat) :
    y ∣ x ↔ x % y = 0 := Nat.dvd_iff_mod_eq_zero

end Prosa.Validation.DivModInterface
