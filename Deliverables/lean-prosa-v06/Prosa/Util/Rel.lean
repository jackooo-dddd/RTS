-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: util/rel.v

import Mathlib.Data.List.Basic

namespace Prosa.Util.Rel

universe u

/-- A function preserves a Boolean relation. -/
def monotone {T : Type u} (R : T → T → Bool) (f : T → T) : Prop :=
  ∀ x y, R x y = true → R (f x) (f y) = true

/-- A Boolean relation is total on the elements observed in a list. -/
def total_over_list {T : Type u} [DecidableEq T]
    (R : T → T → Bool) (xs : List T) : Prop :=
  ∀ x₁ x₂, x₁ ∈ xs → x₂ ∈ xs → R x₁ x₂ = true ∨ R x₂ x₁ = true

/-- A Boolean relation is antisymmetric on the elements observed in a list. -/
def antisymmetric_over_list {T : Type u} [DecidableEq T]
    (R : T → T → Bool) (xs : List T) : Prop :=
  ∀ x₁ x₂,
    x₁ ∈ xs → x₂ ∈ xs →
    R x₁ x₂ = true → R x₂ x₁ = true → x₁ = x₂

end Prosa.Util.Rel
