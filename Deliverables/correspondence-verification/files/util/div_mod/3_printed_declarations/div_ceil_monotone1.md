# `div_ceil_monotone1`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.div_mod.div_ceil_monotone1`
- Lean: `Prosa.Util.Div_mod.div_ceil_monotone1`
- Certificate: `div_ceil_monotone1_statement_certificate`

## Official Rocq

```coq
div_ceil_monotone1 : forall d m n : nat, is_true (m <= n) -> is_true (div_ceil m d <= div_ceil n d)

div_ceil_monotone1 is not universe polymorphic
Arguments div_ceil_monotone1 (d m n)%nat_scope _
div_ceil_monotone1 is opaque
Expands to: Constant prosa.util.div_mod.div_ceil_monotone1
Declared in library prosa.util.div_mod, line 132, characters 6-24
div_ceil_monotone1
     : forall d m n : nat, is_true (m <= n) -> is_true (div_ceil m d <= div_ceil n d)
```

## Lean

```lean
Prosa.Util.Div_mod.div_ceil_monotone1 : ∀ (d m n : ℕ),
  m ≤ n → Prosa.Util.Div_mod.div_ceil m d ≤ Prosa.Util.Div_mod.div_ceil n d
```

## Lean, imported into Rocq

```coq
Prosa_Util_Div_mod_div_ceil_monotone1
     : forall d m n : Nat,
       LE_le_inst1 Nat instLENat m n ->
       LE_le_inst1 Nat instLENat (Prosa_Util_Div_mod_div_ceil m d) (Prosa_Util_Div_mod_div_ceil n d)
```
