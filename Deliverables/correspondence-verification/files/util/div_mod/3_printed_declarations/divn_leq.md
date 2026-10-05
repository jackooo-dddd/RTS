# `divn_leq`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.div_mod.divn_leq`
- Lean: `Prosa.Util.Div_mod.divn_leq`
- Certificate: `divn_leq_statement_certificate`

## Official Rocq

```coq
divn_leq : forall k T x : nat, is_true (k * T <= x < k.+1 * T) -> x %/ T = k

divn_leq is not universe polymorphic
Arguments divn_leq (k T x)%nat_scope _
divn_leq is opaque
Expands to: Constant prosa.util.div_mod.divn_leq
Declared in library prosa.util.div_mod, line 81, characters 6-14
divn_leq
     : forall k T x : nat, is_true (k * T <= x < k.+1 * T) -> x %/ T = k
```

## Lean

```lean
Prosa.Util.Div_mod.divn_leq : ∀ (k T x : ℕ), k * T ≤ x ∧ x < (k + 1) * T → x / T = k
```

## Lean, imported into Rocq

```coq
Prosa_Util_Div_mod_divn_leq
     : forall k T x : Nat,
       And (LE_le_inst1 Nat instLENat (HMul_hMul_inst7 Nat Nat Nat (instHMul_inst1 Nat instMulNat) k T) x)
         (LT_lt_inst1 Nat instLTNat x
            (HMul_hMul_inst7 Nat Nat Nat (instHMul_inst1 Nat instMulNat)
               (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat) k
                  (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1)))
               T)) ->
       @eq Nat (HDiv_hDiv_inst7 Nat Nat Nat (instHDiv_inst1 Nat Nat_instDiv) x T) k
```
