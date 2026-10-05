# `superadditive_standard_equivalence`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.superadditivity.superadditive_standard_equivalence`
- Lean: `Prosa.Util.Superadditivity.superadditive_standard_equivalence`
- Certificate: `superadditivity_equivalence_statement_certificate`

## Official Rocq

```coq
superadditive_standard_equivalence : forall f : nat -> nat, superadditive f <-> superadditive_standard f

superadditive_standard_equivalence is not universe polymorphic
Arguments superadditive_standard_equivalence f%function_scope
superadditive_standard_equivalence is opaque
Expands to: Constant prosa.util.superadditivity.superadditive_standard_equivalence
Declared in library prosa.util.superadditivity, line 39, characters 6-40
superadditive_standard_equivalence
     : forall f : nat -> nat, superadditive f <-> superadditive_standard f
```

## Lean

```lean
Prosa.Util.Superadditivity.superadditive_standard_equivalence : ∀ (f : ℕ → ℕ),
  Prosa.Util.Superadditivity.superadditive f ↔ Prosa.Util.Superadditivity.superadditive_standard f
```

## Lean, imported into Rocq

```coq
Prosa_Util_Superadditivity_superadditive_standard_equivalence
     : forall f : Nat -> Nat,
       Iff (Prosa_Util_Superadditivity_superadditive f) (Prosa_Util_Superadditivity_superadditive_standard f)
```
