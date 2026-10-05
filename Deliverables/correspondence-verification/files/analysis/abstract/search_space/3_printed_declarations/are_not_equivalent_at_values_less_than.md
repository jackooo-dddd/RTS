# `are_not_equivalent_at_values_less_than`

- Kind (Rocq): Definition
- Rocq: `prosa.analysis.abstract.search_space.are_not_equivalent_at_values_less_than`
- Lean: `Prosa.Analysis.Abstract.SearchSpace.are_not_equivalent_at_values_less_than`
- Certificate: `ss_not_equivalent_correspondence`

## Official Rocq

```coq
are_not_equivalent_at_values_less_than :
forall {T : eqType}, (nat -> Equality.sort T) -> (nat -> Equality.sort T) -> nat -> Prop

are_not_equivalent_at_values_less_than is not universe polymorphic
Arguments are_not_equivalent_at_values_less_than {T} (f1 f2)%function_scope B%nat_scope
are_not_equivalent_at_values_less_than is transparent
Expands to: Constant prosa.analysis.abstract.search_space.are_not_equivalent_at_values_less_than
Declared in library prosa.analysis.abstract.search_space, line 39, characters 15-53
@are_not_equivalent_at_values_less_than
     : forall T : eqType, (nat -> Equality.sort T) -> (nat -> Equality.sort T) -> nat -> Prop
```

Body:

```coq
are_not_equivalent_at_values_less_than =
fun (T : eqType) (f1 f2 : nat -> Equality.sort T) (B : nat) =>
exists x : nat, is_true (x < B) /\ f1 x <> f2 x
     : forall {T : eqType}, (nat -> Equality.sort T) -> (nat -> Equality.sort T) -> nat -> Prop

Arguments are_not_equivalent_at_values_less_than {T} (f1 f2)%function_scope B%nat_scope
```

## Lean

```lean
@Prosa.Analysis.Abstract.SearchSpace.are_not_equivalent_at_values_less_than : {T : Type u_1} →
  [DecidableEq T] → (ℕ → T) → (ℕ → T) → ℕ → Prop
def Prosa.Analysis.Abstract.SearchSpace.are_not_equivalent_at_values_less_than.{u} : {T : Type u} →
  [DecidableEq T] → (ℕ → T) → (ℕ → T) → ℕ → Prop :=
fun {T} [DecidableEq T] f1 f2 B => ∃ x < B, f1 x ≠ f2 x
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Abstract_SearchSpace_are_not_equivalent_at_values_less_than
     : forall T : Type, DecidableEq T -> (Nat -> T) -> (Nat -> T) -> Nat -> SProp
```

Body:

```coq
Prosa_Analysis_Abstract_SearchSpace_are_not_equivalent_at_values_less_than@{u Lean.u+1.0} =
fun (T : Type) (_ : DecidableEq T) (f1 f2 : Nat -> T) (B : Nat) =>
Exists Nat (fun x : Nat => And (LT_lt_inst1 Nat instLTNat x B) (Ne T (f1 x) (f2 x)))
     : forall T : Type, DecidableEq T -> (Nat -> T) -> (Nat -> T) -> Nat -> SProp

Arguments Prosa_Analysis_Abstract_SearchSpace_are_not_equivalent_at_values_less_than 
  T%_type_scope inst_3
  (f1 f2)%_function_scope a____at____internal__hyg0%_Nat_scope
```
