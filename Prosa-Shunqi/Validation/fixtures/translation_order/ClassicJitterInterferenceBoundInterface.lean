import Prosa.Classic.Analysis.Global.Jitter.InterferenceBound

/-!
Validation-only interface for `classic/analysis/global/jitter/interference_bound.v` (classic family): kernel-checked Lean
equations, exported with their proofs and used by the Rocq certificate as propositional equations
(transport) only.
-/

namespace Prosa.Validation.ClassicJitterInterferenceBoundInterface

universe u

open Prosa.Util.Sum

theorem production_sumSeq_nil {X : Type u} (F : X → Nat) : sumSeq [] F = 0 := rfl

theorem production_sumSeq_cons {X : Type u} (F : X → Nat) (x : X) (xs : List X) :
    sumSeq (x :: xs) F = F x + sumSeq xs F := by
  simp [sumSeq]

theorem production_sumFiltered_nil {X : Type u} (P : X → Bool) (F : X → Nat) :
    sumFiltered [] P F = 0 := rfl

theorem production_sumFiltered_cons_true {X : Type u} (P : X → Bool) (F : X → Nat)
    (x : X) (xs : List X) (h : P x = true) :
    sumFiltered (x :: xs) P F = F x + sumFiltered xs P F := by
  simp [sumFiltered, h]

theorem production_sumFiltered_cons_false {X : Type u} (P : X → Bool) (F : X → Nat)
    (x : X) (xs : List X) (h : P x = false) :
    sumFiltered (x :: xs) P F = sumFiltered xs P F := by
  simp [sumFiltered, h]

end Prosa.Validation.ClassicJitterInterferenceBoundInterface

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
