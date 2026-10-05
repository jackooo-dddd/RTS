# `slowed_subtraction_value_preservation`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.unit_growth.slowed_subtraction_value_preservation`
- Lean: `Prosa.Util.UnitGrowth.slowed_subtraction_value_preservation`
- Certificate: `slowed_subtraction_value_preservation_statement_certificate`

## Official Rocq

```coq
slowed_subtraction_value_preservation :
forall (f : nat -> nat) (Δ : nat),
@rel.monotone nat leq f -> exists δ : nat, is_true (δ <= Δ) /\ Δ - f Δ = δ - slowed f δ

slowed_subtraction_value_preservation is not universe polymorphic
Arguments slowed_subtraction_value_preservation f%function_scope Δ%nat_scope _
slowed_subtraction_value_preservation is opaque
Expands to: Constant prosa.util.unit_growth.slowed_subtraction_value_preservation
Declared in library prosa.util.unit_growth, line 269, characters 6-43
slowed_subtraction_value_preservation
     : forall (f : nat -> nat) (Δ : nat),
       @rel.monotone nat leq f -> exists δ : nat, is_true (δ <= Δ) /\ Δ - f Δ = δ - slowed f δ
```

## Lean

```lean
Prosa.Util.UnitGrowth.slowed_subtraction_value_preservation : ∀ (f : ℕ → ℕ) (Δ : ℕ),
  Prosa.Util.Rel.monotone (fun x y => decide (x ≤ y)) f → ∃ δ ≤ Δ, Δ - f Δ = δ - Prosa.Util.UnitGrowth.slowed f δ
```

## Lean, imported into Rocq

```coq
Prosa_Util_UnitGrowth_slowed_subtraction_value_preservation
     : forall (f : Nat -> Nat) (_UU0394_ : Nat),
       Prosa_Util_Rel_monotone_inst1 Nat
         (fun x y : Nat => Decidable_decide (LE_le_inst1 Nat instLENat x y) (Nat_decLe x y)) f ->
       Exists Nat
         (fun _UU03b4_ : Nat =>
          And (LE_le_inst1 Nat instLENat _UU03b4_ _UU0394_)
            (@eq Nat (HSub_hSub_inst7 Nat Nat Nat (instHSub_inst1 Nat instSubNat) _UU0394_ (f _UU0394_))
               (HSub_hSub_inst7 Nat Nat Nat (instHSub_inst1 Nat instSubNat) _UU03b4_
                  (Prosa_Util_UnitGrowth_slowed f _UU03b4_))))
```
