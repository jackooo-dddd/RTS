import Prosa.Classic.Implementation.Apa.ArrivalSequence

/-!
Validation-only interface for `classic/implementation/apa/arrival_sequence.v` (classic family): kernel-checked Lean
equations, exported with their proofs and used by the Rocq certificate as propositional equations
(transport) only.
-/

namespace Prosa.Validation.ClassicApaPeriodicArrivalsInterface

open Prosa.Classic.Implementation.Apa.Task.ConcreteTask Prosa.Classic.Implementation.Apa.Job.ConcreteJob

theorem filterMap_nil {num_cpus : Nat} (f : @concrete_task num_cpus → Option (@concrete_job num_cpus)) : List.filterMap f [] = [] := rfl
theorem filterMap_cons_none {num_cpus : Nat} (f : @concrete_task num_cpus → Option (@concrete_job num_cpus)) (a : @concrete_task num_cpus)
    (l : List (@concrete_task num_cpus)) (h : f a = none) : List.filterMap f (a :: l) = List.filterMap f l := by simp [h]
theorem filterMap_cons_some {num_cpus : Nat} (f : @concrete_task num_cpus → Option (@concrete_job num_cpus)) (a : @concrete_task num_cpus)
    (l : List (@concrete_task num_cpus)) (b : @concrete_job num_cpus) (h : f a = some b) :
    List.filterMap f (a :: l) = b :: List.filterMap f l := by simp [h]

end Prosa.Validation.ClassicApaPeriodicArrivalsInterface

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
