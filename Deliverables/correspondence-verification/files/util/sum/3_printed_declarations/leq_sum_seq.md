# `leq_sum_seq`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.sum.leq_sum_seq`
- Lean: `Prosa.Util.Sum.leq_sum_seq`
- Certificate: `leq_sum_seq_statement_certificate`

## Official Rocq

```coq
leq_sum_seq :
forall (I : eqType) (r : seq (Equality.sort I)) (P : pred (Equality.sort I)) (E1 E2 : Equality.sort I -> nat),
(forall i : Equality.sort I, is_true (i \in r) -> is_true (P i) -> is_true (E1 i <= E2 i)) ->
is_true
  (@bigop.bigop.body nat (Equality.sort I) 0 r
     (fun i : Equality.sort I => @bigop.BigBody nat (Equality.sort I) i addn (P i) (E1 i)) <=
   @bigop.bigop.body nat (Equality.sort I) 0 r
     (fun i : Equality.sort I => @bigop.BigBody nat (Equality.sort I) i addn (P i) (E2 i)))

leq_sum_seq is not universe polymorphic
Arguments leq_sum_seq I r%seq_scope P (E1 E2 _)%function_scope
leq_sum_seq is opaque
Expands to: Constant prosa.util.sum.leq_sum_seq
Declared in library prosa.util.sum, line 105, characters 10-21
leq_sum_seq
     : forall (I : eqType) (r : seq (Equality.sort I)) (P : pred (Equality.sort I))
         (E1 E2 : Equality.sort I -> nat),
       (forall i : Equality.sort I, is_true (i \in r) -> is_true (P i) -> is_true (E1 i <= E2 i)) ->
       is_true
         (@bigop.bigop.body nat (Equality.sort I) 0 r
            (fun i : Equality.sort I => @bigop.BigBody nat (Equality.sort I) i addn (P i) (E1 i)) <=
          @bigop.bigop.body nat (Equality.sort I) 0 r
            (fun i : Equality.sort I => @bigop.BigBody nat (Equality.sort I) i addn (P i) (E2 i)))
```

## Lean

```lean
@Prosa.Util.Sum.leq_sum_seq : ∀ {I : Type u_1} [DecidableEq I] (r : List I) (P : I → Bool) (E1 E2 : I → ℕ),
  (∀ i ∈ r, P i = true → E1 i ≤ E2 i) → Prosa.Util.Sum.sumFiltered r P E1 ≤ Prosa.Util.Sum.sumFiltered r P E2
```

## Lean, imported into Rocq

```coq
Prosa_Util_Sum_leq_sum_seq
     : forall I : Type,
       ImportedSumSequence.DecidableEq I ->
       forall (r : ImportedSumSequence.List I) (P : I -> ImportedSumSequence.Bool) (E1 E2 : I -> Nat),
       (forall i : I,
        Membership_mem I (ImportedSumSequence.List I) (List_instMembership I) r i ->
        @eq ImportedSumSequence.Bool (P i) ImportedSumSequence.Bool_true ->
        ImportedSumSequence.LE_le_inst1 Nat ImportedSumSequence.instLENat (E1 i) (E2 i)) ->
       ImportedSumSequence.LE_le_inst1 Nat ImportedSumSequence.instLENat
         (Prosa_Util_Sum_sumFiltered I r P E1) (Prosa_Util_Sum_sumFiltered I r P E2)
```
