# `bigmax_leq_sum`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.sum.bigmax_leq_sum`
- Lean: `Prosa.Util.Sum.bigmax_leq_sum`
- Certificate: `bigmax_leq_sum_statement_certificate`

## Official Rocq

```coq
bigmax_leq_sum :
forall (I : eqType) (r : seq (Equality.sort I)) (P : pred (Equality.sort I)) (F : Equality.sort I -> nat),
is_true
  (@bigop.bigop.body nat (Equality.sort I) 0 r
     (fun i : Equality.sort I => @bigop.BigBody nat (Equality.sort I) i maxn (P i) (F i)) <=
   @bigop.bigop.body nat (Equality.sort I) 0 r
     (fun i : Equality.sort I => @bigop.BigBody nat (Equality.sort I) i addn (P i) (F i)))

bigmax_leq_sum is not universe polymorphic
Arguments bigmax_leq_sum I r%seq_scope P F%function_scope
bigmax_leq_sum is opaque
Expands to: Constant prosa.util.sum.bigmax_leq_sum
Declared in library prosa.util.sum, line 73, characters 10-24
bigmax_leq_sum
     : forall (I : eqType) (r : seq (Equality.sort I)) (P : pred (Equality.sort I))
         (F : Equality.sort I -> nat),
       is_true
         (@bigop.bigop.body nat (Equality.sort I) 0 r
            (fun i : Equality.sort I => @bigop.BigBody nat (Equality.sort I) i maxn (P i) (F i)) <=
          @bigop.bigop.body nat (Equality.sort I) 0 r
            (fun i : Equality.sort I => @bigop.BigBody nat (Equality.sort I) i addn (P i) (F i)))
```

## Lean

```lean
@Prosa.Util.Sum.bigmax_leq_sum : ∀ {I : Type u_1} [DecidableEq I] (r : List I) (P : I → Bool) (F : I → ℕ),
  Prosa.Util.Sum.maxFiltered r P F ≤ Prosa.Util.Sum.sumFiltered r P F
```

## Lean, imported into Rocq

```coq
Prosa_Util_Sum_bigmax_leq_sum
     : forall I : Type,
       ImportedSumSequence.DecidableEq I ->
       forall (r : ImportedSumSequence.List I) (P : I -> ImportedSumSequence.Bool) (F : I -> Nat),
       ImportedSumSequence.LE_le_inst1 Nat ImportedSumSequence.instLENat (Prosa_Util_Sum_maxFiltered I r P F)
         (Prosa_Util_Sum_sumFiltered I r P F)
```
