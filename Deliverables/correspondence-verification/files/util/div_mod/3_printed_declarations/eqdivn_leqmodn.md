# `eqdivn_leqmodn`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.div_mod.eqdivn_leqmodn`
- Lean: `Prosa.Util.Div_mod.eqdivn_leqmodn`
- Certificate: `eqdivn_leqmodn_statement_certificate`

## Official Rocq

```coq
eqdivn_leqmodn :
forall t1 t2 h : nat, is_true (t1 <= t2) -> t1 %/ h = t2 %/ h -> is_true (t1 %% h <= t2 %% h)

eqdivn_leqmodn is not universe polymorphic
Arguments eqdivn_leqmodn (t1 t2 h)%nat_scope _ _
eqdivn_leqmodn is opaque
Expands to: Constant prosa.util.div_mod.eqdivn_leqmodn
Declared in library prosa.util.div_mod, line 8, characters 6-20
eqdivn_leqmodn
     : forall t1 t2 h : nat, is_true (t1 <= t2) -> t1 %/ h = t2 %/ h -> is_true (t1 %% h <= t2 %% h)
```

## Lean

```lean
Prosa.Util.Div_mod.eqdivn_leqmodn : ∀ (t₁ t₂ h : ℕ), t₁ ≤ t₂ → t₁ / h = t₂ / h → t₁ % h ≤ t₂ % h
```

## Lean, imported into Rocq

```coq
Prosa_Util_Div_mod_eqdivn_leqmodn
     : forall t_UU2081_ t_UU2082_ h : Nat,
       LE_le_inst1 Nat instLENat t_UU2081_ t_UU2082_ ->
       @eq Nat (HDiv_hDiv_inst7 Nat Nat Nat (instHDiv_inst1 Nat Nat_instDiv) t_UU2081_ h)
         (HDiv_hDiv_inst7 Nat Nat Nat (instHDiv_inst1 Nat Nat_instDiv) t_UU2082_ h) ->
       LE_le_inst1 Nat instLENat (HMod_hMod_inst7 Nat Nat Nat (instHMod_inst1 Nat Nat_instMod) t_UU2081_ h)
         (HMod_hMod_inst7 Nat Nat Nat (instHMod_inst1 Nat Nat_instMod) t_UU2082_ h)
```
