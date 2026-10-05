# `sum_le_subseq`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.sum.sum_le_subseq`
- Lean: `Prosa.Util.Sum.sum_le_subseq`
- Certificate: `sum_le_subseq_statement_certificate`

## Official Rocq

```coq
sum_le_subseq :
forall (I : eqType) (P : pred (Equality.sort I)) (F : Equality.sort I -> nat) (r1 r2 : seq (Equality.sort I)),
is_true (@subseq I r1 r2) ->
is_true
  (@bigop.bigop.body nat (Equality.sort I) 0 r1
     (fun x : Equality.sort I => @bigop.BigBody nat (Equality.sort I) x addn (P x) (F x)) <=
   @bigop.bigop.body nat (Equality.sort I) 0 r2
     (fun x : Equality.sort I => @bigop.BigBody nat (Equality.sort I) x addn (P x) (F x)))

sum_le_subseq is not universe polymorphic
Arguments sum_le_subseq I P F%function_scope (r1 r2)%seq_scope _
sum_le_subseq is opaque
Expands to: Constant prosa.util.sum.sum_le_subseq
Declared in library prosa.util.sum, line 80, characters 10-23
sum_le_subseq
     : forall (I : eqType) (P : pred (Equality.sort I)) (F : Equality.sort I -> nat)
         (r1 r2 : seq (Equality.sort I)),
       is_true (@subseq I r1 r2) ->
       is_true
         (@bigop.bigop.body nat (Equality.sort I) 0 r1
            (fun x : Equality.sort I => @bigop.BigBody nat (Equality.sort I) x addn (P x) (F x)) <=
          @bigop.bigop.body nat (Equality.sort I) 0 r2
            (fun x : Equality.sort I => @bigop.BigBody nat (Equality.sort I) x addn (P x) (F x)))
```

## Lean

```lean
@Prosa.Util.Sum.sum_le_subseq : ∀ {I : Type u_1} [inst : DecidableEq I] (P : I → Bool) (F : I → ℕ) (r1 r2 : List I),
  Prosa.Util.Sum.subseqb r1 r2 = true → Prosa.Util.Sum.sumFiltered r1 P F ≤ Prosa.Util.Sum.sumFiltered r2 P F
```

## Lean, imported into Rocq

```coq
Prosa_Util_Sum_sum_le_subseq
     : forall (I : Type)
         (inst_3 : ImportedSumSequence.DecidableEq I)
         (P : I -> ImportedSumSequence.Bool) (F : I -> Nat) (r1 r2 : ImportedSumSequence.List I),
       @eq ImportedSumSequence.Bool
         (Prosa_Util_Sum_subseqb I inst_3 r1 r2)
         ImportedSumSequence.Bool_true ->
       ImportedSumSequence.LE_le_inst1 Nat ImportedSumSequence.instLENat
         (Prosa_Util_Sum_sumFiltered I r1 P F) (Prosa_Util_Sum_sumFiltered I r2 P F)
```
