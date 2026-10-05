# `slowed_respects_pointwise_leq`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.unit_growth.slowed_respects_pointwise_leq`
- Lean: `Prosa.Util.UnitGrowth.slowed_respects_pointwise_leq`
- Certificate: `slowed_respects_pointwise_leq_statement_certificate`

## Official Rocq

```coq
slowed_respects_pointwise_leq :
forall (f F : nat -> nat) (Δ : nat),
unit_growth_function f ->
(forall x : nat, is_true (x <= Δ) -> is_true (f x <= F x)) -> is_true (f Δ <= slowed F Δ)

slowed_respects_pointwise_leq is not universe polymorphic
Arguments slowed_respects_pointwise_leq (f F)%function_scope Δ%nat_scope _ _%function_scope
slowed_respects_pointwise_leq is opaque
Expands to: Constant prosa.util.unit_growth.slowed_respects_pointwise_leq
Declared in library prosa.util.unit_growth, line 195, characters 6-35
slowed_respects_pointwise_leq
     : forall (f F : nat -> nat) (Δ : nat),
       unit_growth_function f ->
       (forall x : nat, is_true (x <= Δ) -> is_true (f x <= F x)) -> is_true (f Δ <= slowed F Δ)
```

## Lean

```lean
Prosa.Util.UnitGrowth.slowed_respects_pointwise_leq : ∀ (f F : ℕ → ℕ) (Δ : ℕ),
  Prosa.Util.UnitGrowth.unit_growth_function f → (∀ x ≤ Δ, f x ≤ F x) → f Δ ≤ Prosa.Util.UnitGrowth.slowed F Δ
```

## Lean, imported into Rocq

```coq
Prosa_Util_UnitGrowth_slowed_respects_pointwise_leq
     : forall (f F : Nat -> Nat) (_UU0394_ : Nat),
       Prosa_Util_UnitGrowth_unit_growth_function f ->
       (forall x : Nat, LE_le_inst1 Nat instLENat x _UU0394_ -> LE_le_inst1 Nat instLENat (f x) (F x)) ->
       LE_le_inst1 Nat instLENat (f _UU0394_) (Prosa_Util_UnitGrowth_slowed F _UU0394_)
```
