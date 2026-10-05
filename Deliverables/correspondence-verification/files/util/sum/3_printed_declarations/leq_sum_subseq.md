# `leq_sum_subseq`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.sum.leq_sum_subseq`
- Lean: `Prosa.Util.Sum.leq_sum_subseq`
- Certificate: `leq_sum_subseq_statement_certificate`

## Official Rocq

```coq
leq_sum_subseq :
forall (I : eqType) (r r' : seq (Equality.sort I)) (P : pred (Equality.sort I)) (F : Equality.sort I -> nat),
is_true (@subseq I r r') ->
is_true
  (@bigop.bigop.body nat (Equality.sort I) 0 r
     (fun i : Equality.sort I => @bigop.BigBody nat (Equality.sort I) i addn (P i) (F i)) <=
   @bigop.bigop.body nat (Equality.sort I) 0 r'
     (fun i : Equality.sort I => @bigop.BigBody nat (Equality.sort I) i addn (P i) (F i)))

leq_sum_subseq is not universe polymorphic
Arguments leq_sum_subseq I (r r')%seq_scope P F%function_scope _
leq_sum_subseq is opaque
Expands to: Constant prosa.util.sum.leq_sum_subseq
Declared in library prosa.util.sum, line 147, characters 6-20
leq_sum_subseq
     : forall (I : eqType) (r r' : seq (Equality.sort I)) (P : pred (Equality.sort I))
         (F : Equality.sort I -> nat),
       is_true (@subseq I r r') ->
       is_true
         (@bigop.bigop.body nat (Equality.sort I) 0 r
            (fun i : Equality.sort I => @bigop.BigBody nat (Equality.sort I) i addn (P i) (F i)) <=
          @bigop.bigop.body nat (Equality.sort I) 0 r'
            (fun i : Equality.sort I => @bigop.BigBody nat (Equality.sort I) i addn (P i) (F i)))
```

## Lean

```lean
@Prosa.Util.Sum.leq_sum_subseq : ∀ {I : Type u_1} [inst : DecidableEq I] (r r' : List I) (P : I → Bool) (F : I → ℕ),
  Prosa.Util.Sum.subseqb r r' = true → Prosa.Util.Sum.sumFiltered r P F ≤ Prosa.Util.Sum.sumFiltered r' P F
```

## Lean, imported into Rocq

```coq
Prosa_Util_Sum_leq_sum_subseq
     : forall (I : Type)
         (inst_3 : ImportedSumSequence.DecidableEq I)
         (r r' : ImportedSumSequence.List I) (P : I -> ImportedSumSequence.Bool) 
         (F : I -> Nat),
       @eq ImportedSumSequence.Bool
         (Prosa_Util_Sum_subseqb I inst_3 r r')
         ImportedSumSequence.Bool_true ->
       ImportedSumSequence.LE_le_inst1 Nat ImportedSumSequence.instLENat (Prosa_Util_Sum_sumFiltered I r P F)
         (Prosa_Util_Sum_sumFiltered I r' P F)
```
