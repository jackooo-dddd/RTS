# `addmod_le_mod`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.div_mod.addmod_le_mod`
- Lean: `Prosa.Util.Div_mod.addmod_le_mod`
- Certificate: `addmod_le_mod_statement_certificate`

## Official Rocq

```coq
addmod_le_mod : forall x y h : nat, is_true (0 < h) -> x %/ h = (x + y) %/ h -> is_true (x %% h + y %% h < h)

addmod_le_mod is not universe polymorphic
Arguments addmod_le_mod (x y h)%nat_scope _ _
addmod_le_mod is opaque
Expands to: Constant prosa.util.div_mod.addmod_le_mod
Declared in library prosa.util.div_mod, line 68, characters 6-19
addmod_le_mod
     : forall x y h : nat, is_true (0 < h) -> x %/ h = (x + y) %/ h -> is_true (x %% h + y %% h < h)
```

## Lean

```lean
Prosa.Util.Div_mod.addmod_le_mod : ∀ (x y h : ℕ), 0 < h → x / h = (x + y) / h → x % h + y % h < h
```

## Lean, imported into Rocq

```coq
Prosa_Util_Div_mod_addmod_le_mod
     : forall x y h : Nat,
       LT_lt_inst1 Nat instLTNat (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0)) h ->
       @eq Nat (HDiv_hDiv_inst7 Nat Nat Nat (instHDiv_inst1 Nat Nat_instDiv) x h)
         (HDiv_hDiv_inst7 Nat Nat Nat (instHDiv_inst1 Nat Nat_instDiv)
            (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat) x y) h) ->
       LT_lt_inst1 Nat instLTNat
         (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat)
            (HMod_hMod_inst7 Nat Nat Nat (instHMod_inst1 Nat Nat_instMod) x h)
            (HMod_hMod_inst7 Nat Nat Nat (instHMod_inst1 Nat Nat_instMod) y h))
         h
```
