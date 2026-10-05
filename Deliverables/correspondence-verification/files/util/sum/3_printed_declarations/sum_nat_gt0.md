# `sum_nat_gt0`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.sum.sum_nat_gt0`
- Lean: `Prosa.Util.Sum.sum_nat_gt0`
- Certificate: `sum_nat_gt0_statement_certificate`

## Official Rocq

```coq
sum_nat_gt0 :
forall (I : eqType) (r : seq (Equality.sort I)) (P : pred (Equality.sort I)) (F : Equality.sort I -> nat),
(0 <
 @bigop.bigop.body nat (Equality.sort I) 0 r
   (fun i : Equality.sort I => @bigop.BigBody nat (Equality.sort I) i addn (P i) (F i))) =
@has (Equality.sort I) (fun x : Equality.sort I => 0 < F x) [seq x <- r | P x]

sum_nat_gt0 is not universe polymorphic
Arguments sum_nat_gt0 I r%seq_scope P F%function_scope
sum_nat_gt0 is opaque
Expands to: Constant prosa.util.sum.sum_nat_gt0
Declared in library prosa.util.sum, line 36, characters 10-21
sum_nat_gt0
     : forall (I : eqType) (r : seq (Equality.sort I)) (P : pred (Equality.sort I))
         (F : Equality.sort I -> nat),
       (0 <
        @bigop.bigop.body nat (Equality.sort I) 0 r
          (fun i : Equality.sort I => @bigop.BigBody nat (Equality.sort I) i addn (P i) (F i))) =
       @has (Equality.sort I) (fun x : Equality.sort I => 0 < F x) [seq x <- r | P x]
```

## Lean

```lean
@Prosa.Util.Sum.sum_nat_gt0 : ∀ {I : Type u_1} [DecidableEq I] (r : List I) (P : I → Bool) (F : I → ℕ),
  decide (0 < Prosa.Util.Sum.sumFiltered r P F) = r.any fun x => P x && decide (0 < F x)
```

## Lean, imported into Rocq

```coq
Prosa_Util_Sum_sum_nat_gt0
     : forall I : Type,
       ImportedSumSequence.DecidableEq I ->
       forall (r : ImportedSumSequence.List I) (P : I -> ImportedSumSequence.Bool) (F : I -> Nat),
       @eq ImportedSumSequence.Bool
         (ImportedSumSequence.Decidable_decide
            (ImportedSumSequence.LT_lt_inst1 Nat ImportedSumSequence.instLTNat
               (ImportedSumSequence.OfNat_ofNat_inst1 Nat 0 (ImportedSumSequence.instOfNatNat 0))
               (Prosa_Util_Sum_sumFiltered I r P F))
            (Nat_decLt (ImportedSumSequence.OfNat_ofNat_inst1 Nat 0 (ImportedSumSequence.instOfNatNat 0))
               (Prosa_Util_Sum_sumFiltered I r P F)))
         (List_any I r
            (fun x : I =>
             ImportedSumSequence.Bool_and (P x)
               (ImportedSumSequence.Decidable_decide
                  (ImportedSumSequence.LT_lt_inst1 Nat ImportedSumSequence.instLTNat
                     (ImportedSumSequence.OfNat_ofNat_inst1 Nat 0 (ImportedSumSequence.instOfNatNat 0)) 
                     (F x))
                  (Nat_decLt
                     (ImportedSumSequence.OfNat_ofNat_inst1 Nat 0 (ImportedSumSequence.instOfNatNat 0)) 
                     (F x)))))
```
