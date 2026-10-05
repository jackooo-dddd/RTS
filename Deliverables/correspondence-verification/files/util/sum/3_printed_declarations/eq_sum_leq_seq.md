# `eq_sum_leq_seq`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.sum.eq_sum_leq_seq`
- Lean: `Prosa.Util.Sum.eq_sum_leq_seq`
- Certificate: `eq_sum_leq_seq_statement_certificate`

## Official Rocq

```coq
eq_sum_leq_seq :
forall (I : eqType) (r : seq (Equality.sort I)) (P : pred (Equality.sort I)) (E1 E2 : Equality.sort I -> nat),
(forall i : Equality.sort I, is_true (i \in r) -> is_true (P i) -> is_true (E1 i <= E2 i)) ->
(@bigop.bigop.body nat (Equality.sort I) 0 r
   (fun x : Equality.sort I => @bigop.BigBody nat (Equality.sort I) x addn (P x) (E1 x)) ==
 @bigop.bigop.body nat (Equality.sort I) 0 r
   (fun x : Equality.sort I => @bigop.BigBody nat (Equality.sort I) x addn (P x) (E2 x))) =
@all (Equality.sort I) (fun x : Equality.sort I => E1 x == E2 x) [seq x <- r | P x]

eq_sum_leq_seq is not universe polymorphic
Arguments eq_sum_leq_seq I r%seq_scope P (E1 E2 _)%function_scope
eq_sum_leq_seq is opaque
Expands to: Constant prosa.util.sum.eq_sum_leq_seq
Declared in library prosa.util.sum, line 215, characters 8-22
eq_sum_leq_seq
     : forall (I : eqType) (r : seq (Equality.sort I)) (P : pred (Equality.sort I))
         (E1 E2 : Equality.sort I -> nat),
       (forall i : Equality.sort I, is_true (i \in r) -> is_true (P i) -> is_true (E1 i <= E2 i)) ->
       (@bigop.bigop.body nat (Equality.sort I) 0 r
          (fun x : Equality.sort I => @bigop.BigBody nat (Equality.sort I) x addn (P x) (E1 x)) ==
        @bigop.bigop.body nat (Equality.sort I) 0 r
          (fun x : Equality.sort I => @bigop.BigBody nat (Equality.sort I) x addn (P x) (E2 x))) =
       @all (Equality.sort I) (fun x : Equality.sort I => E1 x == E2 x) [seq x <- r | P x]
```

## Lean

```lean
@Prosa.Util.Sum.eq_sum_leq_seq : ∀ {I : Type u_1} [DecidableEq I] (r : List I) (P : I → Bool) (E1 E2 : I → ℕ),
  (∀ i ∈ r, P i = true → E1 i ≤ E2 i) →
    decide (Prosa.Util.Sum.sumFiltered r P E1 = Prosa.Util.Sum.sumFiltered r P E2) =
      r.all fun x => !P x || decide (E1 x = E2 x)
```

## Lean, imported into Rocq

```coq
Prosa_Util_Sum_eq_sum_leq_seq
     : forall I : Type,
       ImportedSumSequence.DecidableEq I ->
       forall (r : ImportedSumSequence.List I) (P : I -> ImportedSumSequence.Bool) (E1 E2 : I -> Nat),
       (forall i : I,
        Membership_mem I (ImportedSumSequence.List I) (List_instMembership I) r i ->
        @eq ImportedSumSequence.Bool (P i) ImportedSumSequence.Bool_true ->
        ImportedSumSequence.LE_le_inst1 Nat ImportedSumSequence.instLENat (E1 i) (E2 i)) ->
       @eq ImportedSumSequence.Bool
         (ImportedSumSequence.Decidable_decide
            (@eq Nat (Prosa_Util_Sum_sumFiltered I r P E1) (Prosa_Util_Sum_sumFiltered I r P E2))
            (ImportedSumSequence.instDecidableEqNat (Prosa_Util_Sum_sumFiltered I r P E1)
               (Prosa_Util_Sum_sumFiltered I r P E2)))
         (List_all I r
            (fun x : I =>
             Bool_or (Bool_not (P x))
               (ImportedSumSequence.Decidable_decide (@eq Nat (E1 x) (E2 x))
                  (ImportedSumSequence.instDecidableEqNat (E1 x) (E2 x)))))
```
