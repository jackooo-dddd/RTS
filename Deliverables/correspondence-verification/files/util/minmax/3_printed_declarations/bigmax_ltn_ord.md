# `bigmax_ltn_ord`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.minmax.bigmax_ltn_ord`
- Lean: `Prosa.Util.Minmax.bigmax_ltn_ord`
- Certificate: `bigmax_ltn_ord_statement_certificate`

## Official Rocq

```coq
bigmax_ltn_ord :
forall (n : nat) (P : pred nat) (i0 : fintype.ordinal n),
is_true (P (@fintype.nat_of_ord n i0)) ->
is_true
  (@bigop.bigop.body nat (fintype.Finite.sort (fintype.fintype_ordinal__canonical__fintype_Finite n)) 0
     (bigop.index_enum (fintype.fintype_ordinal__canonical__fintype_Finite n))
     (fun i : fintype.ordinal n =>
      @bigop.BigBody nat (fintype.ordinal n) i maxn (P (@fintype.nat_of_ord n i)) (@fintype.nat_of_ord n i)) <
   n)

bigmax_ltn_ord is not universe polymorphic
Arguments bigmax_ltn_ord n%nat_scope P i0 _
bigmax_ltn_ord is opaque
Expands to: Constant prosa.util.minmax.bigmax_ltn_ord
Declared in library prosa.util.minmax, line 75, characters 6-20
bigmax_ltn_ord
     : forall (n : nat) (P : pred nat) (i0 : fintype.ordinal n),
       is_true (P (@fintype.nat_of_ord n i0)) ->
       is_true
         (@bigop.bigop.body nat (fintype.Finite.sort (fintype.fintype_ordinal__canonical__fintype_Finite n))
            0 (bigop.index_enum (fintype.fintype_ordinal__canonical__fintype_Finite n))
            (fun i : fintype.ordinal n =>
             @bigop.BigBody nat (fintype.ordinal n) i maxn (P (@fintype.nat_of_ord n i))
               (@fintype.nat_of_ord n i)) <
          n)
```

## Lean

```lean
Prosa.Util.Minmax.bigmax_ltn_ord : ∀ (n : ℕ) (P : ℕ → Bool) (i₀ : Fin n),
  P ↑i₀ = true → Prosa.Util.Minmax.bigMaxNatRange n P < n
```

## Lean, imported into Rocq

```coq
Prosa_Util_Minmax_bigmax_ltn_ord
     : forall (n : Nat) (P : Nat -> Bool) (i_UU2080_ : Fin n),
       @eq Bool (P (Fin_val n i_UU2080_)) Bool_true ->
       LT_lt_inst1 Nat instLTNat (Prosa_Util_Minmax_bigMaxNatRange n P) n
```
