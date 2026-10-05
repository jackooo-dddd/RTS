# `div_ceil_subadditive`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.div_mod.div_ceil_subadditive`
- Lean: `Prosa.Util.Div_mod.div_ceil_subadditive`
- Certificate: `div_ceil_subadditive_statement_certificate`

## Official Rocq

```coq
div_ceil_subadditive : forall T : nat, subadditive (div_ceil^~ T)

div_ceil_subadditive is not universe polymorphic
Arguments div_ceil_subadditive T%nat_scope h a b _
div_ceil_subadditive is opaque
Expands to: Constant prosa.util.div_mod.div_ceil_subadditive
Declared in library prosa.util.div_mod, line 170, characters 6-26
div_ceil_subadditive
     : forall T : nat, subadditive (div_ceil^~ T)
```

## Lean

```lean
Prosa.Util.Div_mod.div_ceil_subadditive : ∀ (T : ℕ),
  Prosa.Util.Subadditivity.subadditive fun x => Prosa.Util.Div_mod.div_ceil x T
```

## Lean, imported into Rocq

```coq
Prosa_Util_Div_mod_div_ceil_subadditive
     : forall T : Nat, Prosa_Util_Subadditivity_subadditive (fun x : Nat => Prosa_Util_Div_mod_div_ceil x T)
```
