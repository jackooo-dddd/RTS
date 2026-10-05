# `div_ceil_multiple`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.div_mod.div_ceil_multiple`
- Lean: `Prosa.Util.Div_mod.div_ceil_multiple`
- Certificate: `div_ceil_multiple_statement_certificate`

## Official Rocq

```coq
div_ceil_multiple : forall Δ T n : nat, is_true (0 < T) -> is_true (T * n < Δ) -> is_true (n < div_ceil Δ T)

div_ceil_multiple is not universe polymorphic
Arguments div_ceil_multiple (Δ T n)%nat_scope _ _
div_ceil_multiple is opaque
Expands to: Constant prosa.util.div_mod.div_ceil_multiple
Declared in library prosa.util.div_mod, line 193, characters 6-23
div_ceil_multiple
     : forall Δ T n : nat, is_true (0 < T) -> is_true (T * n < Δ) -> is_true (n < div_ceil Δ T)
```

## Lean

```lean
Prosa.Util.Div_mod.div_ceil_multiple : ∀ (delta T n : ℕ),
  0 < T → T * n < delta → n < Prosa.Util.Div_mod.div_ceil delta T
```

## Lean, imported into Rocq

```coq
Prosa_Util_Div_mod_div_ceil_multiple
     : forall delta T n : Nat,
       LT_lt_inst1 Nat instLTNat (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0)) T ->
       LT_lt_inst1 Nat instLTNat (HMul_hMul_inst7 Nat Nat Nat (instHMul_inst1 Nat instMulNat) T n) delta ->
       LT_lt_inst1 Nat instLTNat n (Prosa_Util_Div_mod_div_ceil delta T)
```
