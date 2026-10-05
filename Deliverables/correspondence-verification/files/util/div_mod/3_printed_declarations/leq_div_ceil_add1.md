# `leq_div_ceil_add1`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.div_mod.leq_div_ceil_add1`
- Lean: `Prosa.Util.Div_mod.leq_div_ceil_add1`
- Certificate: `leq_div_ceil_add1_statement_certificate`

## Official Rocq

```coq
leq_div_ceil_add1 :
forall Δ T : nat, is_true (0 < T) -> is_true (T <= Δ) -> is_true (div_ceil (Δ - T) T < div_ceil Δ T)

leq_div_ceil_add1 is not universe polymorphic
Arguments leq_div_ceil_add1 (Δ T)%nat_scope _ _
leq_div_ceil_add1 is opaque
Expands to: Constant prosa.util.div_mod.leq_div_ceil_add1
Declared in library prosa.util.div_mod, line 150, characters 6-23
leq_div_ceil_add1
     : forall Δ T : nat, is_true (0 < T) -> is_true (T <= Δ) -> is_true (div_ceil (Δ - T) T < div_ceil Δ T)
```

## Lean

```lean
Prosa.Util.Div_mod.leq_div_ceil_add1 : ∀ (delta T : ℕ),
  0 < T → T ≤ delta → Prosa.Util.Div_mod.div_ceil (delta - T) T < Prosa.Util.Div_mod.div_ceil delta T
```

## Lean, imported into Rocq

```coq
Prosa_Util_Div_mod_leq_div_ceil_add1
     : forall delta T : Nat,
       LT_lt_inst1 Nat instLTNat (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0)) T ->
       LE_le_inst1 Nat instLENat T delta ->
       LT_lt_inst1 Nat instLTNat
         (Prosa_Util_Div_mod_div_ceil (HSub_hSub_inst7 Nat Nat Nat (instHSub_inst1 Nat instSubNat) delta T) T)
         (Prosa_Util_Div_mod_div_ceil delta T)
```
