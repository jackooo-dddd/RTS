# `ltn_sum_leq_seq`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.sum.ltn_sum_leq_seq`
- Lean: `Prosa.Util.Sum.ltn_sum_leq_seq`
- Certificate: `ltn_sum_leq_seq_statement_certificate`

## Official Rocq

```coq
ltn_sum_leq_seq :
forall (I : eqType) (r : seq (Equality.sort I)) (P : pred (Equality.sort I)) (E1 E2 : Equality.sort I -> nat)
  (j : Equality.sort I),
is_true (j \in r) ->
is_true (P j) ->
is_true (E1 j < E2 j) ->
(forall i : Equality.sort I, is_true (i \in r) -> is_true (P i) -> is_true (E1 i <= E2 i)) ->
is_true
  (@bigop.bigop.body nat (Equality.sort I) 0 r
     (fun x : Equality.sort I => @bigop.BigBody nat (Equality.sort I) x addn (P x) (E1 x)) <
   @bigop.bigop.body nat (Equality.sort I) 0 r
     (fun x : Equality.sort I => @bigop.BigBody nat (Equality.sort I) x addn (P x) (E2 x)))

ltn_sum_leq_seq is not universe polymorphic
Arguments ltn_sum_leq_seq I r%seq_scope P (E1 E2)%function_scope j _ _ _ _%function_scope
ltn_sum_leq_seq is opaque
Expands to: Constant prosa.util.sum.ltn_sum_leq_seq
Declared in library prosa.util.sum, line 199, characters 8-23
ltn_sum_leq_seq
     : forall (I : eqType) (r : seq (Equality.sort I)) (P : pred (Equality.sort I))
         (E1 E2 : Equality.sort I -> nat) (j : Equality.sort I),
       is_true (j \in r) ->
       is_true (P j) ->
       is_true (E1 j < E2 j) ->
       (forall i : Equality.sort I, is_true (i \in r) -> is_true (P i) -> is_true (E1 i <= E2 i)) ->
       is_true
         (@bigop.bigop.body nat (Equality.sort I) 0 r
            (fun x : Equality.sort I => @bigop.BigBody nat (Equality.sort I) x addn (P x) (E1 x)) <
          @bigop.bigop.body nat (Equality.sort I) 0 r
            (fun x : Equality.sort I => @bigop.BigBody nat (Equality.sort I) x addn (P x) (E2 x)))
```

## Lean

```lean
@Prosa.Util.Sum.ltn_sum_leq_seq : ∀ {I : Type u_1} [DecidableEq I] (r : List I) (P : I → Bool) (E1 E2 : I → ℕ),
  ∀ j ∈ r,
    P j = true →
      E1 j < E2 j →
        (∀ i ∈ r, P i = true → E1 i ≤ E2 i) → Prosa.Util.Sum.sumFiltered r P E1 < Prosa.Util.Sum.sumFiltered r P E2
```

## Lean, imported into Rocq

```coq
Prosa_Util_Sum_ltn_sum_leq_seq
     : forall I : Type,
       ImportedSumSequence.DecidableEq I ->
       forall (r : ImportedSumSequence.List I) (P : I -> ImportedSumSequence.Bool) (E1 E2 : I -> Nat) (j : I),
       Membership_mem I (ImportedSumSequence.List I) (List_instMembership I) r j ->
       @eq ImportedSumSequence.Bool (P j) ImportedSumSequence.Bool_true ->
       ImportedSumSequence.LT_lt_inst1 Nat ImportedSumSequence.instLTNat (E1 j) (E2 j) ->
       (forall i : I,
        Membership_mem I (ImportedSumSequence.List I) (List_instMembership I) r i ->
        @eq ImportedSumSequence.Bool (P i) ImportedSumSequence.Bool_true ->
        ImportedSumSequence.LE_le_inst1 Nat ImportedSumSequence.instLENat (E1 i) (E2 i)) ->
       ImportedSumSequence.LT_lt_inst1 Nat ImportedSumSequence.instLTNat
         (Prosa_Util_Sum_sumFiltered I r P E1) (Prosa_Util_Sum_sumFiltered I r P E2)
```
