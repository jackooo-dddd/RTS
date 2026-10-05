# `addn1_modn_commute`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.div_mod.addn1_modn_commute`
- Lean: `Prosa.Util.Div_mod.addn1_modn_commute`
- Certificate: `addn1_modn_commute_statement_certificate`

## Official Rocq

```coq
addn1_modn_commute : forall x h : nat, is_true (0 < h) -> x %/ h = (x + 1) %/ h -> (x + 1) %% h = x %% h + 1

addn1_modn_commute is not universe polymorphic
Arguments addn1_modn_commute (x h)%nat_scope _ _
addn1_modn_commute is opaque
Expands to: Constant prosa.util.div_mod.addn1_modn_commute
Declared in library prosa.util.div_mod, line 53, characters 6-24
addn1_modn_commute
     : forall x h : nat, is_true (0 < h) -> x %/ h = (x + 1) %/ h -> (x + 1) %% h = x %% h + 1
```

## Lean

```lean
Prosa.Util.Div_mod.addn1_modn_commute : ∀ (x h : ℕ), 0 < h → x / h = (x + 1) / h → (x + 1) % h = x % h + 1
```

## Lean, imported into Rocq

```coq
Prosa_Util_Div_mod_addn1_modn_commute
     : forall x h : Nat,
       LT_lt_inst1 Nat instLTNat (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0)) h ->
       @eq Nat (HDiv_hDiv_inst7 Nat Nat Nat (instHDiv_inst1 Nat Nat_instDiv) x h)
         (HDiv_hDiv_inst7 Nat Nat Nat (instHDiv_inst1 Nat Nat_instDiv)
            (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat) x
               (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1)))
            h) ->
       @eq Nat
         (HMod_hMod_inst7 Nat Nat Nat (instHMod_inst1 Nat Nat_instMod)
            (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat) x
               (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1)))
            h)
         (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat)
            (HMod_hMod_inst7 Nat Nat Nat (instHMod_inst1 Nat Nat_instMod) x h)
            (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1)))
```
