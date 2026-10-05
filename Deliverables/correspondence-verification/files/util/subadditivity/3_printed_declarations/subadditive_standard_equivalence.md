# `subadditive_standard_equivalence`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.subadditivity.subadditive_standard_equivalence`
- Lean: `Prosa.Util.Subadditivity.subadditive_standard_equivalence`
- Certificate: `subadditive_standard_equivalence_statement_certificate`

## Official Rocq

```coq
subadditive_standard_equivalence : forall f : nat -> nat, subadditive f <-> subadditive_standard f

subadditive_standard_equivalence is not universe polymorphic
Arguments subadditive_standard_equivalence f%function_scope
subadditive_standard_equivalence is opaque
Expands to: Constant prosa.util.subadditivity.subadditive_standard_equivalence
Declared in library prosa.util.subadditivity, line 38, characters 6-38
subadditive_standard_equivalence
     : forall f : nat -> nat, subadditive f <-> subadditive_standard f
```

## Lean

```lean
Prosa.Util.Subadditivity.subadditive_standard_equivalence : ∀ (f : ℕ → ℕ),
  Prosa.Util.Subadditivity.subadditive f ↔ Prosa.Util.Subadditivity.subadditive_standard f
```

## Lean, imported into Rocq

```coq
Prosa_Util_Subadditivity_subadditive_standard_equivalence
     : forall f : Nat -> Nat,
       Iff (Prosa_Util_Subadditivity_subadditive f) (Prosa_Util_Subadditivity_subadditive_standard f)
```
