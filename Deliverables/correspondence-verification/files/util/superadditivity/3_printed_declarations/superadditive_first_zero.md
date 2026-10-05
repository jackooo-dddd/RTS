# `superadditive_first_zero`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.superadditivity.superadditive_first_zero`
- Lean: `Prosa.Util.Superadditivity.superadditive_first_zero`
- Certificate: `superadditivity_first_zero_statement_certificate`

## Official Rocq

```coq
superadditive_first_zero : forall f : nat -> nat, superadditive_at f 0 -> f 0 = 0

superadditive_first_zero is not universe polymorphic
Arguments superadditive_first_zero f%function_scope _
superadditive_first_zero is opaque
Expands to: Constant prosa.util.superadditivity.superadditive_first_zero
Declared in library prosa.util.superadditivity, line 59, characters 8-32
superadditive_first_zero
     : forall f : nat -> nat, superadditive_at f 0 -> f 0 = 0
```

## Lean

```lean
Prosa.Util.Superadditivity.superadditive_first_zero : ∀ (f : ℕ → ℕ),
  Prosa.Util.Superadditivity.superadditive_at f 0 → f 0 = 0
```

## Lean, imported into Rocq

```coq
Prosa_Util_Superadditivity_superadditive_first_zero
     : forall f : Nat -> Nat,
       Prosa_Util_Superadditivity_superadditive_at f (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0)) ->
       @eq Nat (f (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0))) (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0))
```
