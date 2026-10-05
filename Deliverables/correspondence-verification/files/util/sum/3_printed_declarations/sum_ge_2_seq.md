# `sum_ge_2_seq`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.sum.sum_ge_2_seq`
- Lean: `Prosa.Util.Sum.sum_ge_2_seq`
- Certificate: `sum_ge_2_seq_statement_certificate`

## Official Rocq

```coq
sum_ge_2_seq :
forall {X : eqType} (xs : seq (Equality.sort X)) (p : Equality.sort X -> nat),
is_true (@uniq X xs) ->
(forall x : Equality.sort X, is_true (x \in xs) -> is_true (p x <= 1)) ->
is_true
  (1 <
   @bigop.bigop.body nat (Equality.sort X) 0 xs
     (fun x : Equality.sort X => @bigop.BigBody nat (Equality.sort X) x addn true (p x))) ->
exists x1 x2 : Equality.sort X,
  is_true (x1 != x2) /\
  is_true (x1 \in xs) /\ is_true (x2 \in xs) /\ is_true (p x1 == 1) /\ is_true (p x2 == 1)

sum_ge_2_seq is not universe polymorphic
Arguments sum_ge_2_seq {X} xs%seq_scope p%function_scope _ _%function_scope _
sum_ge_2_seq is opaque
Expands to: Constant prosa.util.sum.sum_ge_2_seq
Declared in library prosa.util.sum, line 486, characters 6-18
@sum_ge_2_seq
     : forall (X : eqType) (xs : seq (Equality.sort X)) (p : Equality.sort X -> nat),
       is_true (@uniq X xs) ->
       (forall x : Equality.sort X, is_true (x \in xs) -> is_true (p x <= 1)) ->
       is_true
         (1 <
          @bigop.bigop.body nat (Equality.sort X) 0 xs
            (fun x : Equality.sort X => @bigop.BigBody nat (Equality.sort X) x addn true (p x))) ->
       exists x1 x2 : Equality.sort X,
         is_true (x1 != x2) /\
         is_true (x1 \in xs) /\ is_true (x2 \in xs) /\ is_true (p x1 == 1) /\ is_true (p x2 == 1)
```

## Lean

```lean
@Prosa.Util.Sum.sum_ge_2_seq : ∀ {X : Type u_1} [inst : DecidableEq X] (xs : List X) (p : X → ℕ),
  xs.Nodup →
    (∀ x ∈ xs, p x ≤ 1) →
      2 ≤ Prosa.Util.Sum.sumSeq xs p →
        ∃ x1 x2, decide (x1 ≠ x2) = true ∧ x1 ∈ xs ∧ x2 ∈ xs ∧ decide (p x1 = 1) = true ∧ decide (p x2 = 1) = true
```

## Lean, imported into Rocq

```coq
Prosa_Util_Sum_sum_ge_2_seq
     : forall (X : Type)
         (inst_3 : ImportedSumSequence.DecidableEq X)
         (xs : ImportedSumSequence.List X) (p : X -> Nat),
       List_Nodup X xs ->
       (forall x : X,
        Membership_mem X (ImportedSumSequence.List X) (List_instMembership X) xs x ->
        ImportedSumSequence.LE_le_inst1 Nat ImportedSumSequence.instLENat (p x)
          (ImportedSumSequence.OfNat_ofNat_inst1 Nat 1 (ImportedSumSequence.instOfNatNat 1))) ->
       ImportedSumSequence.LE_le_inst1 Nat ImportedSumSequence.instLENat
         (ImportedSumSequence.OfNat_ofNat_inst1 Nat 2 (ImportedSumSequence.instOfNatNat 2))
         (Prosa_Util_Sum_sumSeq X xs p) ->
       ImportedSumSequence.Exists X
         (fun x1 : X =>
          ImportedSumSequence.Exists X
            (fun x2 : X =>
             And
               (@eq ImportedSumSequence.Bool
                  (ImportedSumSequence.Decidable_decide (Ne X x1 x2)
                     (instDecidableNot (@eq X x1 x2)
                        (inst_3 x1 x2)))
                  ImportedSumSequence.Bool_true)
               (And (Membership_mem X (ImportedSumSequence.List X) (List_instMembership X) xs x1)
                  (And (Membership_mem X (ImportedSumSequence.List X) (List_instMembership X) xs x2)
                     (And
                        (@eq ImportedSumSequence.Bool
                           (ImportedSumSequence.Decidable_decide
                              (@eq Nat (p x1)
                                 (ImportedSumSequence.OfNat_ofNat_inst1 Nat 1
                                    (ImportedSumSequence.instOfNatNat 1)))
                              (ImportedSumSequence.instDecidableEqNat (p x1)
                                 (ImportedSumSequence.OfNat_ofNat_inst1 Nat 1
                                    (ImportedSumSequence.instOfNatNat 1))))
                           ImportedSumSequence.Bool_true)
                        (@eq ImportedSumSequence.Bool
                           (ImportedSumSequence.Decidable_decide
                              (@eq Nat (p x2)
                                 (ImportedSumSequence.OfNat_ofNat_inst1 Nat 1
                                    (ImportedSumSequence.instOfNatNat 1)))
                              (ImportedSumSequence.instDecidableEqNat (p x2)
                                 (ImportedSumSequence.OfNat_ofNat_inst1 Nat 1
                                    (ImportedSumSequence.instOfNatNat 1))))
                           ImportedSumSequence.Bool_true))))))
```
