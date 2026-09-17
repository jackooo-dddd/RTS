-- Translated from: ../rt-proofs/util/rel.v
import Mathlib.Data.List.Basic

namespace Prosa.Util.Rel

section Relations

  variable {T : Type _}

  def monotone (f : T → T) (R : T → T → Bool) : Prop :=
    ∀ x y, R x y → R (f x) (f y)

end Relations

section Order

  variable {T : Type _} [DecidableEq T]
  variable (rel : T → T → Bool)
  variable (l : List T)

  def total_over_list : Prop :=
    ∀ x1 x2,
      x1 ∈ l →
      x2 ∈ l →
      (rel x1 x2 ∨ rel x2 x1)

  def antisymmetric_over_list : Prop :=
    ∀ x1 x2,
      x1 ∈ l →
      x2 ∈ l →
      rel x1 x2 →
      rel x2 x1 →
      x1 = x2

end Order

end Prosa.Util.Rel
