# `leq_sum_seq_pred`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.sum.leq_sum_seq_pred`
- Lean: `Prosa.Util.Sum.leq_sum_seq_pred`
- Certificate: `leq_sum_seq_pred_statement_certificate`

## Official Rocq

```coq
leq_sum_seq_pred :
forall (I : eqType) (r : seq (Equality.sort I)) (E : Equality.sort I -> nat) (P1 P2 : pred (Equality.sort I)),
(forall i : Equality.sort I, is_true (i \in r) -> is_true (P1 i) -> is_true (P2 i)) ->
is_true
  (@bigop.bigop.body nat (Equality.sort I) 0 r
     (fun i : Equality.sort I => @bigop.BigBody nat (Equality.sort I) i addn (P1 i) (E i)) <=
   @bigop.bigop.body nat (Equality.sort I) 0 r
     (fun i : Equality.sort I => @bigop.BigBody nat (Equality.sort I) i addn (P2 i) (E i)))

leq_sum_seq_pred is not universe polymorphic
Arguments leq_sum_seq_pred I r%seq_scope E%function_scope P1 P2 _%function_scope
leq_sum_seq_pred is opaque
Expands to: Constant prosa.util.sum.leq_sum_seq_pred
Declared in library prosa.util.sum, line 127, characters 10-26
leq_sum_seq_pred
     : forall (I : eqType) (r : seq (Equality.sort I)) (E : Equality.sort I -> nat)
         (P1 P2 : pred (Equality.sort I)),
       (forall i : Equality.sort I, is_true (i \in r) -> is_true (P1 i) -> is_true (P2 i)) ->
       is_true
         (@bigop.bigop.body nat (Equality.sort I) 0 r
            (fun i : Equality.sort I => @bigop.BigBody nat (Equality.sort I) i addn (P1 i) (E i)) <=
          @bigop.bigop.body nat (Equality.sort I) 0 r
            (fun i : Equality.sort I => @bigop.BigBody nat (Equality.sort I) i addn (P2 i) (E i)))
```

## Lean

```lean
@Prosa.Util.Sum.leq_sum_seq_pred : ∀ {I : Type u_1} [DecidableEq I] (r : List I) (E : I → ℕ) (P1 P2 : I → Bool),
  (∀ i ∈ r, P1 i = true → P2 i = true) → Prosa.Util.Sum.sumFiltered r P1 E ≤ Prosa.Util.Sum.sumFiltered r P2 E
```

## Lean, imported into Rocq

```coq
Prosa_Util_Sum_leq_sum_seq_pred
     : forall I : Type,
       ImportedSumSequence.DecidableEq I ->
       forall (r : ImportedSumSequence.List I) (E : I -> Nat) (P1 P2 : I -> ImportedSumSequence.Bool),
       (forall i : I,
        Membership_mem I (ImportedSumSequence.List I) (List_instMembership I) r i ->
        @eq ImportedSumSequence.Bool (P1 i) ImportedSumSequence.Bool_true ->
        @eq ImportedSumSequence.Bool (P2 i) ImportedSumSequence.Bool_true) ->
       ImportedSumSequence.LE_le_inst1 Nat ImportedSumSequence.instLENat
         (Prosa_Util_Sum_sumFiltered I r P1 E) (Prosa_Util_Sum_sumFiltered I r P2 E)
```
