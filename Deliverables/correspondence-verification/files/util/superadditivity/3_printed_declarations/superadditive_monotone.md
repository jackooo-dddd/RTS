# `superadditive_monotone`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.superadditivity.superadditive_monotone`
- Lean: `Prosa.Util.Superadditivity.superadditive_monotone`
- Certificate: `superadditivity_monotone_statement_certificate`

## Official Rocq

```coq
superadditive_monotone : forall f : nat -> nat, superadditive f -> @monotone nat leq f

superadditive_monotone is not universe polymorphic
Arguments superadditive_monotone f%function_scope h_superadditive x y _
superadditive_monotone is opaque
Expands to: Constant prosa.util.superadditivity.superadditive_monotone
Declared in library prosa.util.superadditivity, line 78, characters 10-32
superadditive_monotone
     : forall f : nat -> nat, superadditive f -> @monotone nat leq f
```

## Lean

```lean
Prosa.Util.Superadditivity.superadditive_monotone : ∀ (f : ℕ → ℕ),
  Prosa.Util.Superadditivity.superadditive f → Prosa.Util.Rel.monotone (fun a b => decide (a ≤ b)) f
```

## Lean, imported into Rocq

```coq
Prosa_Util_Superadditivity_superadditive_monotone
     : forall f : Nat -> Nat,
       Prosa_Util_Superadditivity_superadditive f ->
       Prosa_Util_Rel_monotone_inst1 Nat
         (fun a b : Nat => Decidable_decide (LE_le_inst1 Nat instLENat a b) (Nat_decLe a b)) f
```
