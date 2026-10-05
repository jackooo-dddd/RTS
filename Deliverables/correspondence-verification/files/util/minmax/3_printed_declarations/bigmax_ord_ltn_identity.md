# `bigmax_ord_ltn_identity`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.minmax.bigmax_ord_ltn_identity`
- Lean: `Prosa.Util.Minmax.bigmax_ord_ltn_identity`
- Certificate: `bigmax_ord_ltn_identity_statement_certificate`

## Official Rocq

```coq
bigmax_ord_ltn_identity :
forall n : nat,
is_true (0 < n) ->
is_true
  (@bigop.bigop.body nat (fintype.Finite.sort (fintype.fintype_ordinal__canonical__fintype_Finite n)) 0
     (bigop.index_enum (fintype.fintype_ordinal__canonical__fintype_Finite n))
     (fun i : fintype.ordinal n =>
      @bigop.BigBody nat (fintype.ordinal n) i maxn true (@fintype.nat_of_ord n i)) <
   n)

bigmax_ord_ltn_identity is not universe polymorphic
Arguments bigmax_ord_ltn_identity n%nat_scope _
bigmax_ord_ltn_identity is opaque
Expands to: Constant prosa.util.minmax.bigmax_ord_ltn_identity
Declared in library prosa.util.minmax, line 59, characters 6-29
bigmax_ord_ltn_identity
     : forall n : nat,
       is_true (0 < n) ->
       is_true
         (@bigop.bigop.body nat (fintype.Finite.sort (fintype.fintype_ordinal__canonical__fintype_Finite n))
            0 (bigop.index_enum (fintype.fintype_ordinal__canonical__fintype_Finite n))
            (fun i : fintype.ordinal n =>
             @bigop.BigBody nat (fintype.ordinal n) i maxn true (@fintype.nat_of_ord n i)) <
          n)
```

## Lean

```lean
Prosa.Util.Minmax.bigmax_ord_ltn_identity : ∀ n > 0, (Prosa.Util.Minmax.bigMaxNatRange n fun x => true) < n
```

## Lean, imported into Rocq

```coq
Prosa_Util_Minmax_bigmax_ord_ltn_identity
     : forall n : Nat,
       GT_gt_inst1 Nat instLTNat n (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0)) ->
       LT_lt_inst1 Nat instLTNat (Prosa_Util_Minmax_bigMaxNatRange n (fun _ : Nat => Bool_true)) n
```
