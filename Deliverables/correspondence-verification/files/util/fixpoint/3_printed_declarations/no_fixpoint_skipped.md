# `no_fixpoint_skipped`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.fixpoint.no_fixpoint_skipped`
- Lean: `Prosa.Util.Fixpoint.no_fixpoint_skipped`
- Certificate: `fixpoint_no_skipped_statement_certificate`

## Official Rocq

```coq
no_fixpoint_skipped :
forall f : nat -> nat,
@monotone nat leq f ->
is_true (0 < f 1) -> forall a c : nat, c = f a -> forall b : nat, is_true (a <= b < c) -> is_true (b != f b)

no_fixpoint_skipped is not universe polymorphic
Arguments no_fixpoint_skipped f%function_scope H_f_mono F1 (a c)%nat_scope _ b%nat_scope _
no_fixpoint_skipped is opaque
Expands to: Constant prosa.util.fixpoint.no_fixpoint_skipped
Declared in library prosa.util.fixpoint, line 74, characters 10-29
no_fixpoint_skipped
     : forall f : nat -> nat,
       @monotone nat leq f ->
       is_true (0 < f 1) ->
       forall a c : nat, c = f a -> forall b : nat, is_true (a <= b < c) -> is_true (b != f b)
```

## Lean

```lean
Prosa.Util.Fixpoint.no_fixpoint_skipped : ∀ (f : ℕ → ℕ),
  Prosa.Util.Rel.monotone (fun a b => decide (a ≤ b)) f →
    0 < f 1 → ∀ (a c : ℕ), c = f a → ∀ (b : ℕ), a ≤ b → b < c → b ≠ f b
```

## Lean, imported into Rocq

```coq
Prosa_Util_Fixpoint_no_fixpoint_skipped
     : forall f : Nat -> Nat,
       Prosa_Util_Rel_monotone_inst1 Nat
         (fun a b : Nat => Decidable_decide (LE_le_inst1 Nat instLENat a b) (Nat_decLe a b)) f ->
       LT_lt_inst1 Nat instLTNat (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0))
         (f (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1))) ->
       forall a c : Nat,
       @eq Nat c (f a) ->
       forall b : Nat, LE_le_inst1 Nat instLENat a b -> LT_lt_inst1 Nat instLTNat b c -> Ne Nat b (f b)
```
