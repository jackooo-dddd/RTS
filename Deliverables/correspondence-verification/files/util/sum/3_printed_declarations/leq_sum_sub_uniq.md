# `leq_sum_sub_uniq`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.sum.leq_sum_sub_uniq`
- Lean: `Prosa.Util.Sum.leq_sum_sub_uniq`
- Certificate: `leq_sum_sub_uniq_statement_certificate`

## Official Rocq

```coq
leq_sum_sub_uniq :
forall (I : eqType) (r : seq (Equality.sort I)) (F : Equality.sort I -> nat) (rs : seq (Equality.sort I)),
is_true (@uniq I r) ->
{subset r <= rs} ->
is_true
  (@bigop.bigop.body nat (Equality.sort I) 0 r
     (fun i : Equality.sort I => @bigop.BigBody nat (Equality.sort I) i addn true (F i)) <=
   @bigop.bigop.body nat (Equality.sort I) 0 rs
     (fun i : Equality.sort I => @bigop.BigBody nat (Equality.sort I) i addn true (F i)))

leq_sum_sub_uniq is not universe polymorphic
Arguments leq_sum_sub_uniq I r%seq_scope F%function_scope rs%seq_scope _ _
leq_sum_sub_uniq is opaque
Expands to: Constant prosa.util.sum.leq_sum_sub_uniq
Declared in library prosa.util.sum, line 164, characters 6-22
leq_sum_sub_uniq
     : forall (I : eqType) (r : seq (Equality.sort I)) (F : Equality.sort I -> nat)
         (rs : seq (Equality.sort I)),
       is_true (@uniq I r) ->
       {subset r <= rs} ->
       is_true
         (@bigop.bigop.body nat (Equality.sort I) 0 r
            (fun i : Equality.sort I => @bigop.BigBody nat (Equality.sort I) i addn true (F i)) <=
          @bigop.bigop.body nat (Equality.sort I) 0 rs
            (fun i : Equality.sort I => @bigop.BigBody nat (Equality.sort I) i addn true (F i)))
```

## Lean

```lean
@Prosa.Util.Sum.leq_sum_sub_uniq : ∀ {I : Type u_1} [DecidableEq I] (r : List I) (F : I → ℕ) (rs : List I),
  r.Nodup → (∀ x ∈ r, x ∈ rs) → Prosa.Util.Sum.sumSeq r F ≤ Prosa.Util.Sum.sumSeq rs F
```

## Lean, imported into Rocq

```coq
Prosa_Util_Sum_leq_sum_sub_uniq
     : forall I : Type,
       ImportedSumSequence.DecidableEq I ->
       forall (r : ImportedSumSequence.List I) (F : I -> Nat) (rs : ImportedSumSequence.List I),
       List_Nodup I r ->
       (forall x : I,
        Membership_mem I (ImportedSumSequence.List I) (List_instMembership I) r x ->
        Membership_mem I (ImportedSumSequence.List I) (List_instMembership I) rs x) ->
       ImportedSumSequence.LE_le_inst1 Nat ImportedSumSequence.instLENat (Prosa_Util_Sum_sumSeq I r F)
         (Prosa_Util_Sum_sumSeq I rs F)
```
