# `mod_elim`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.div_mod.mod_elim`
- Lean: `Prosa.Util.Div_mod.mod_elim`
- Certificate: `mod_elim_statement_certificate`

## Official Rocq

```coq
mod_elim :
forall a b c : nat,
is_true (b < c) -> (a + c - b) %% c = (if b <= a %% c then a %% c - b else a %% c + c - b)

mod_elim is not universe polymorphic
Arguments mod_elim (a b c)%nat_scope _
mod_elim is opaque
Expands to: Constant prosa.util.div_mod.mod_elim
Declared in library prosa.util.div_mod, line 224, characters 6-14
mod_elim
     : forall a b c : nat,
       is_true (b < c) -> (a + c - b) %% c = (if b <= a %% c then a %% c - b else a %% c + c - b)
```

## Lean

```lean
Prosa.Util.Div_mod.mod_elim : ∀ (a b c : ℕ), b < c → (a + c - b) % c = if b ≤ a % c then a % c - b else a % c + c - b
```

## Lean, imported into Rocq

```coq
Prosa_Util_Div_mod_mod_elim
     : forall a b c : Nat,
       LT_lt_inst1 Nat instLTNat b c ->
       @eq Nat
         (HMod_hMod_inst7 Nat Nat Nat (instHMod_inst1 Nat Nat_instMod)
            (HSub_hSub_inst7 Nat Nat Nat (instHSub_inst1 Nat instSubNat)
               (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat) a c) b)
            c)
         (ite Nat
            (LE_le_inst1 Nat instLENat b (HMod_hMod_inst7 Nat Nat Nat (instHMod_inst1 Nat Nat_instMod) a c))
            (Nat_decLe b (HMod_hMod_inst7 Nat Nat Nat (instHMod_inst1 Nat Nat_instMod) a c))
            (HSub_hSub_inst7 Nat Nat Nat (instHSub_inst1 Nat instSubNat)
               (HMod_hMod_inst7 Nat Nat Nat (instHMod_inst1 Nat Nat_instMod) a c) b)
            (HSub_hSub_inst7 Nat Nat Nat (instHSub_inst1 Nat instSubNat)
               (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat)
                  (HMod_hMod_inst7 Nat Nat Nat (instHMod_inst1 Nat Nat_instMod) a c) c)
               b))
```
