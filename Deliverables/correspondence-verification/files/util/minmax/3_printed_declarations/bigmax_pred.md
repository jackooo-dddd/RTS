# `bigmax_pred`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.minmax.bigmax_pred`
- Lean: `Prosa.Util.Minmax.bigmax_pred`
- Certificate: `bigmax_pred_statement_certificate`

## Official Rocq

```coq
bigmax_pred :
forall (n : nat) (P : pred nat) (i0 : fintype.ordinal n),
is_true (P (@fintype.nat_of_ord n i0)) ->
is_true
  (P
     (@bigop.bigop.body nat (fintype.Finite.sort (fintype.fintype_ordinal__canonical__fintype_Finite n)) 0
        (bigop.index_enum (fintype.fintype_ordinal__canonical__fintype_Finite n))
        (fun i : fintype.ordinal n =>
         @bigop.BigBody nat (fintype.ordinal n) i maxn (P (@fintype.nat_of_ord n i))
           (@fintype.nat_of_ord n i))))

bigmax_pred is not universe polymorphic
Arguments bigmax_pred n%nat_scope P i0 _
bigmax_pred is opaque
Expands to: Constant prosa.util.minmax.bigmax_pred
Declared in library prosa.util.minmax, line 93, characters 6-17
bigmax_pred
     : forall (n : nat) (P : pred nat) (i0 : fintype.ordinal n),
       is_true (P (@fintype.nat_of_ord n i0)) ->
       is_true
         (P
            (@bigop.bigop.body nat
               (fintype.Finite.sort (fintype.fintype_ordinal__canonical__fintype_Finite n)) 0
               (bigop.index_enum (fintype.fintype_ordinal__canonical__fintype_Finite n))
               (fun i : fintype.ordinal n =>
                @bigop.BigBody nat (fintype.ordinal n) i maxn (P (@fintype.nat_of_ord n i))
                  (@fintype.nat_of_ord n i))))
```

## Lean

```lean
Prosa.Util.Minmax.bigmax_pred : ∀ (n : ℕ) (P : ℕ → Bool) (i₀ : Fin n),
  P ↑i₀ = true → P (Prosa.Util.Minmax.bigMaxNatRange n P) = true
```

## Lean, imported into Rocq

```coq
Prosa_Util_Minmax_bigmax_pred
     : forall (n : Nat) (P : Nat -> Bool) (i_UU2080_ : Fin n),
       @eq Bool (P (Fin_val n i_UU2080_)) Bool_true ->
       @eq Bool (P (Prosa_Util_Minmax_bigMaxNatRange n P)) Bool_true
```
