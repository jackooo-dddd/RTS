# `slowed_respects_monotone`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.unit_growth.slowed_respects_monotone`
- Lean: `Prosa.Util.UnitGrowth.slowed_respects_monotone`
- Certificate: `slowed_respects_monotone_statement_certificate`

## Official Rocq

```coq
slowed_respects_monotone : forall f : nat -> nat, @rel.monotone nat leq f -> @rel.monotone nat leq (slowed f)

slowed_respects_monotone is not universe polymorphic
Arguments slowed_respects_monotone f%function_scope _ x y _
slowed_respects_monotone is opaque
Expands to: Constant prosa.util.unit_growth.slowed_respects_monotone
Declared in library prosa.util.unit_growth, line 223, characters 6-30
slowed_respects_monotone
     : forall f : nat -> nat, @rel.monotone nat leq f -> @rel.monotone nat leq (slowed f)
```

## Lean

```lean
Prosa.Util.UnitGrowth.slowed_respects_monotone : ∀ (f : ℕ → ℕ),
  Prosa.Util.Rel.monotone (fun x y => decide (x ≤ y)) f →
    Prosa.Util.Rel.monotone (fun x y => decide (x ≤ y)) (Prosa.Util.UnitGrowth.slowed f)
```

## Lean, imported into Rocq

```coq
Prosa_Util_UnitGrowth_slowed_respects_monotone
     : forall f : Nat -> Nat,
       Prosa_Util_Rel_monotone_inst1 Nat
         (fun x y : Nat => Decidable_decide (LE_le_inst1 Nat instLENat x y) (Nat_decLe x y)) f ->
       Prosa_Util_Rel_monotone_inst1 Nat
         (fun x y : Nat => Decidable_decide (LE_le_inst1 Nat instLENat x y) (Nat_decLe x y))
         (Prosa_Util_UnitGrowth_slowed f)
```
