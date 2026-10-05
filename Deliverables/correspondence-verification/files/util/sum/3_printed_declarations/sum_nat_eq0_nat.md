# `sum_nat_eq0_nat`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.sum.sum_nat_eq0_nat`
- Lean: `Prosa.Util.Sum.sum_nat_eq0_nat`
- Certificate: `sum_nat_eq0_nat_statement_certificate`

## Official Rocq

```coq
sum_nat_eq0_nat :
forall (I : eqType) (r : seq (Equality.sort I)) (P : pred (Equality.sort I)) (F : Equality.sort I -> nat),
(@bigop.bigop.body nat (Equality.sort I) 0 r
   (fun i : Equality.sort I => @bigop.BigBody nat (Equality.sort I) i addn (P i) (F i)) ==
 0) =
@all (Equality.sort I) (fun x : Equality.sort I => F x == 0) [seq x <- r | P x]

sum_nat_eq0_nat is not universe polymorphic
Arguments sum_nat_eq0_nat I r%seq_scope P F%function_scope
sum_nat_eq0_nat is opaque
Expands to: Constant prosa.util.sum.sum_nat_eq0_nat
Declared in library prosa.util.sum, line 27, characters 10-25
sum_nat_eq0_nat
     : forall (I : eqType) (r : seq (Equality.sort I)) (P : pred (Equality.sort I))
         (F : Equality.sort I -> nat),
       (@bigop.bigop.body nat (Equality.sort I) 0 r
          (fun i : Equality.sort I => @bigop.BigBody nat (Equality.sort I) i addn (P i) (F i)) ==
        0) =
       @all (Equality.sort I) (fun x : Equality.sort I => F x == 0) [seq x <- r | P x]
```

## Lean

```lean
@Prosa.Util.Sum.sum_nat_eq0_nat : ∀ {I : Type u_1} [DecidableEq I] (r : List I) (P : I → Bool) (F : I → ℕ),
  decide (Prosa.Util.Sum.sumFiltered r P F = 0) = r.all fun x => !P x || decide (F x = 0)
```

## Lean, imported into Rocq

```coq
Prosa_Util_Sum_sum_nat_eq0_nat
     : forall I : Type,
       ImportedSumSequence.DecidableEq I ->
       forall (r : ImportedSumSequence.List I) (P : I -> ImportedSumSequence.Bool) (F : I -> Nat),
       @eq ImportedSumSequence.Bool
         (ImportedSumSequence.Decidable_decide
            (@eq Nat (Prosa_Util_Sum_sumFiltered I r P F)
               (ImportedSumSequence.OfNat_ofNat_inst1 Nat 0 (ImportedSumSequence.instOfNatNat 0)))
            (ImportedSumSequence.instDecidableEqNat (Prosa_Util_Sum_sumFiltered I r P F)
               (ImportedSumSequence.OfNat_ofNat_inst1 Nat 0 (ImportedSumSequence.instOfNatNat 0))))
         (List_all I r
            (fun x : I =>
             Bool_or (Bool_not (P x))
               (ImportedSumSequence.Decidable_decide
                  (@eq Nat (F x)
                     (ImportedSumSequence.OfNat_ofNat_inst1 Nat 0 (ImportedSumSequence.instOfNatNat 0)))
                  (ImportedSumSequence.instDecidableEqNat (F x)
                     (ImportedSumSequence.OfNat_ofNat_inst1 Nat 0 (ImportedSumSequence.instOfNatNat 0))))))
```
