# `div_floor_add_g`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.div_mod.div_floor_add_g`
- Lean: `Prosa.Util.Div_mod.div_floor_add_g`
- Certificate: `div_floor_add_g_statement_certificate`

## Official Rocq

```coq
div_floor_add_g : forall a b : nat, is_true (0 < b) -> is_true (a < a %/ b * b + b)

div_floor_add_g is not universe polymorphic
Arguments div_floor_add_g (a b)%nat_scope _
div_floor_add_g is opaque
Expands to: Constant prosa.util.div_mod.div_floor_add_g
Declared in library prosa.util.div_mod, line 209, characters 6-21
div_floor_add_g
     : forall a b : nat, is_true (0 < b) -> is_true (a < a %/ b * b + b)
```

## Lean

```lean
Prosa.Util.Div_mod.div_floor_add_g : ∀ (a b : ℕ), 0 < b → a < Prosa.Util.Div_mod.div_floor a b * b + b
```

## Lean, imported into Rocq

```coq
Prosa_Util_Div_mod_div_floor_add_g
     : forall a b : Nat,
       LT_lt_inst1 Nat instLTNat (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0)) b ->
       LT_lt_inst1 Nat instLTNat a
         (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat)
            (HMul_hMul_inst7 Nat Nat Nat (instHMul_inst1 Nat instMulNat) (Prosa_Util_Div_mod_div_floor a b) b)
            b)
```
