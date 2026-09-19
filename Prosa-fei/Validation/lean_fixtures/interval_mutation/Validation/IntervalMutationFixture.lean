import Mathlib.Algebra.BigOperators.Intervals

namespace Validation.IntervalMutationFixture

open scoped BigOperators

def originalIcoSum (m n : Nat) (F : Nat → Nat) : Nat :=
  ∑ i ∈ Finset.Ico m n, F i

def mutatedIccSum (m n : Nat) (F : Nat → Nat) : Nat :=
  ∑ i ∈ Finset.Icc m n, F i

/-- Positive control: helper introduction and a different surface expression,
    but exactly the original half-open interval semantics. -/
def positiveControlSum (m n : Nat) (F : Nat → Nat) : Nat :=
  let interval := Finset.Ico m n
  interval.sum F

end Validation.IntervalMutationFixture
