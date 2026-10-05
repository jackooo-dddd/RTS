# `div_ceil0`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.div_mod.div_ceil0`
- Lean: `Prosa.Util.Div_mod.div_ceil0`
- Certificate: `div_ceil0_statement_certificate`

## Official Rocq

```coq
div_ceil0 : forall b : nat, div_ceil 0 b = 0

div_ceil0 is not universe polymorphic
Arguments div_ceil0 b%nat_scope
div_ceil0 is opaque
Expands to: Constant prosa.util.div_mod.div_ceil0
Declared in library prosa.util.div_mod, line 110, characters 6-15
div_ceil0
     : forall b : nat, div_ceil 0 b = 0
```

## Lean

```lean
Prosa.Util.Div_mod.div_ceil0 : ∀ (b : ℕ), Prosa.Util.Div_mod.div_ceil 0 b = 0
```

## Lean, imported into Rocq

```coq
Prosa_Util_Div_mod_div_ceil0
     : forall b : Nat,
       @eq Nat (Prosa_Util_Div_mod_div_ceil (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0)) b)
         (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0))
```
