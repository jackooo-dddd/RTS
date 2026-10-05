# `div_ceil_gt0`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.div_mod.div_ceil_gt0`
- Lean: `Prosa.Util.Div_mod.div_ceil_gt0`
- Certificate: `div_ceil_gt0_statement_certificate`

## Official Rocq

```coq
div_ceil_gt0 : forall a b : nat, is_true (0 < a) -> is_true (0 < b) -> is_true (0 < div_ceil a b)

div_ceil_gt0 is not universe polymorphic
Arguments div_ceil_gt0 (a b)%nat_scope _ _
div_ceil_gt0 is opaque
Expands to: Constant prosa.util.div_mod.div_ceil_gt0
Declared in library prosa.util.div_mod, line 119, characters 6-18
div_ceil_gt0
     : forall a b : nat, is_true (0 < a) -> is_true (0 < b) -> is_true (0 < div_ceil a b)
```

## Lean

```lean
Prosa.Util.Div_mod.div_ceil_gt0 : ∀ (a b : ℕ), 0 < a → 0 < b → 0 < Prosa.Util.Div_mod.div_ceil a b
```

## Lean, imported into Rocq

```coq
Prosa_Util_Div_mod_div_ceil_gt0
     : forall a b : Nat,
       LT_lt_inst1 Nat instLTNat (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0)) a ->
       LT_lt_inst1 Nat instLTNat (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0)) b ->
       LT_lt_inst1 Nat instLTNat (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0)) (Prosa_Util_Div_mod_div_ceil a b)
```
