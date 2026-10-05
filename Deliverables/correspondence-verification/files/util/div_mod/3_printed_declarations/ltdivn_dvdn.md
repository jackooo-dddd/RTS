# `ltdivn_dvdn`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.div_mod.ltdivn_dvdn`
- Lean: `Prosa.Util.Div_mod.ltdivn_dvdn`
- Certificate: `ltdivn_dvdn_statement_certificate`

## Official Rocq

```coq
ltdivn_dvdn : forall x y : nat, is_true (x %/ y < (x + 1) %/ y) -> is_true (y %| x + 1)

ltdivn_dvdn is not universe polymorphic
Arguments ltdivn_dvdn (x y)%nat_scope _
ltdivn_dvdn is opaque
Expands to: Constant prosa.util.div_mod.ltdivn_dvdn
Declared in library prosa.util.div_mod, line 30, characters 6-17
ltdivn_dvdn
     : forall x y : nat, is_true (x %/ y < (x + 1) %/ y) -> is_true (y %| x + 1)
```

## Lean

```lean
Prosa.Util.Div_mod.ltdivn_dvdn : ∀ (x y : ℕ), x / y < (x + 1) / y → y ∣ x + 1
```

## Lean, imported into Rocq

```coq
Prosa_Util_Div_mod_ltdivn_dvdn
     : forall x y : Nat,
       LT_lt_inst1 Nat instLTNat (HDiv_hDiv_inst7 Nat Nat Nat (instHDiv_inst1 Nat Nat_instDiv) x y)
         (HDiv_hDiv_inst7 Nat Nat Nat (instHDiv_inst1 Nat Nat_instDiv)
            (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat) x
               (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1)))
            y) ->
       Dvd_dvd_inst1 Nat Nat_instDvd y
         (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat) x
            (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1)))
```
