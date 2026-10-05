# `exists_intermediate_point`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.unit_growth.exists_intermediate_point`
- Lean: `Prosa.Util.UnitGrowth.exists_intermediate_point`
- Certificate: `exists_intermediate_point_statement_certificate`

## Official Rocq

```coq
exists_intermediate_point :
forall f : nat -> nat,
unit_growth_function f ->
forall x1 x2 : nat,
is_true (x1 <= x2) ->
forall y : nat, is_true (f x1 <= y < f x2) -> exists x_mid : nat, is_true (x1 <= x_mid < x2) /\ f x_mid = y

exists_intermediate_point is not universe polymorphic
Arguments exists_intermediate_point f%function_scope H_unit_growth_function (x1 x2)%nat_scope 
  H_is_interval y%nat_scope H_between
exists_intermediate_point is opaque
Expands to: Constant prosa.util.unit_growth.exists_intermediate_point
Declared in library prosa.util.unit_growth, line 44, characters 10-35
exists_intermediate_point
     : forall f : nat -> nat,
       unit_growth_function f ->
       forall x1 x2 : nat,
       is_true (x1 <= x2) ->
       forall y : nat,
       is_true (f x1 <= y < f x2) -> exists x_mid : nat, is_true (x1 <= x_mid < x2) /\ f x_mid = y
```

## Lean

```lean
Prosa.Util.UnitGrowth.exists_intermediate_point : ∀ (f : ℕ → ℕ),
  Prosa.Util.UnitGrowth.unit_growth_function f →
    ∀ (x1 x2 : ℕ), x1 ≤ x2 → ∀ (y : ℕ), f x1 ≤ y ∧ y < f x2 → ∃ xmid, (x1 ≤ xmid ∧ xmid < x2) ∧ f xmid = y
```

## Lean, imported into Rocq

```coq
Prosa_Util_UnitGrowth_exists_intermediate_point
     : forall f : Nat -> Nat,
       Prosa_Util_UnitGrowth_unit_growth_function f ->
       forall x1 x2 : Nat,
       LE_le_inst1 Nat instLENat x1 x2 ->
       forall y : Nat,
       And (LE_le_inst1 Nat instLENat (f x1) y) (LT_lt_inst1 Nat instLTNat y (f x2)) ->
       Exists Nat
         (fun xmid : Nat =>
          And (And (LE_le_inst1 Nat instLENat x1 xmid) (LT_lt_inst1 Nat instLTNat xmid x2))
            (@eq Nat (f xmid) y))
```
