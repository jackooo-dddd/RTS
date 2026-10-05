# `slowed_never_exceeds`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.unit_growth.slowed_never_exceeds`
- Lean: `Prosa.Util.UnitGrowth.slowed_never_exceeds`
- Certificate: `slowed_never_exceeds_statement_certificate`

## Official Rocq

```coq
slowed_never_exceeds : forall (f : nat -> nat) (x : nat), is_true (slowed f x <= f x)

slowed_never_exceeds is not universe polymorphic
Arguments slowed_never_exceeds f%function_scope x%nat_scope
slowed_never_exceeds is opaque
Expands to: Constant prosa.util.unit_growth.slowed_never_exceeds
Declared in library prosa.util.unit_growth, line 241, characters 6-26
slowed_never_exceeds
     : forall (f : nat -> nat) (x : nat), is_true (slowed f x <= f x)
```

## Lean

```lean
Prosa.Util.UnitGrowth.slowed_never_exceeds : ∀ (f : ℕ → ℕ) (x : ℕ), Prosa.Util.UnitGrowth.slowed f x ≤ f x
```

## Lean, imported into Rocq

```coq
Prosa_Util_UnitGrowth_slowed_never_exceeds
     : forall (f : Nat -> Nat) (x : Nat), LE_le_inst1 Nat instLENat (Prosa_Util_UnitGrowth_slowed f x) (f x)
```
