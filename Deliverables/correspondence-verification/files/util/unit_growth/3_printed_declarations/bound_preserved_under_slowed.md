# `bound_preserved_under_slowed`

- Kind (Rocq): Corollary
- Rocq: `prosa.util.unit_growth.bound_preserved_under_slowed`
- Lean: `Prosa.Util.UnitGrowth.bound_preserved_under_slowed`
- Certificate: `bound_preserved_under_slowed_statement_certificate`

## Official Rocq

```coq
bound_preserved_under_slowed :
forall (f : nat -> nat) (δ A F : nat), is_true (A <= F - f δ) -> is_true (A <= F - slowed f δ)

bound_preserved_under_slowed is not universe polymorphic
Arguments bound_preserved_under_slowed f%function_scope (δ A F)%nat_scope _
bound_preserved_under_slowed is opaque
Expands to: Constant prosa.util.unit_growth.bound_preserved_under_slowed
Declared in library prosa.util.unit_growth, line 250, characters 10-38
bound_preserved_under_slowed
     : forall (f : nat -> nat) (δ A F : nat), is_true (A <= F - f δ) -> is_true (A <= F - slowed f δ)
```

## Lean

```lean
Prosa.Util.UnitGrowth.bound_preserved_under_slowed : ∀ (f : ℕ → ℕ) (δ A F : ℕ),
  A ≤ F - f δ → A ≤ F - Prosa.Util.UnitGrowth.slowed f δ
```

## Lean, imported into Rocq

```coq
Prosa_Util_UnitGrowth_bound_preserved_under_slowed
     : forall (f : Nat -> Nat) (_UU03b4_ A F : Nat),
       LE_le_inst1 Nat instLENat A
         (HSub_hSub_inst7 Nat Nat Nat (instHSub_inst1 Nat instSubNat) F (f _UU03b4_)) ->
       LE_le_inst1 Nat instLENat A
         (HSub_hSub_inst7 Nat Nat Nat (instHSub_inst1 Nat instSubNat) F
            (Prosa_Util_UnitGrowth_slowed f _UU03b4_))
```
