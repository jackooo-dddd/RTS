# `sum_split_exhaustive_mutually_exclusive_preds`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.sum.sum_split_exhaustive_mutually_exclusive_preds`
- Lean: `Prosa.Util.Sum.sum_split_exhaustive_mutually_exclusive_preds`
- Certificate: `sum_split_exhaustive_mutually_exclusive_preds_statement_certificate`

## Official Rocq

```coq
sum_split_exhaustive_mutually_exclusive_preds :
forall (I : eqType) (r : seq (Equality.sort I)) (P : pred (Equality.sort I)) (F : Equality.sort I -> nat)
  (Q R : Equality.sort I -> bool),
(forall x : Equality.sort I, P x = Q x || R x) ->
(forall x : Equality.sort I, is_true (~~ (Q x && R x))) ->
@bigop.bigop.body nat (Equality.sort I) 0 r
  (fun r0 : Equality.sort I => @bigop.BigBody nat (Equality.sort I) r0 addn (P r0) (F r0)) =
@bigop.bigop.body nat (Equality.sort I) 0 r
  (fun r0 : Equality.sort I => @bigop.BigBody nat (Equality.sort I) r0 addn (Q r0) (F r0)) +
@bigop.bigop.body nat (Equality.sort I) 0 r
  (fun r0 : Equality.sort I => @bigop.BigBody nat (Equality.sort I) r0 addn (R r0) (F r0))

sum_split_exhaustive_mutually_exclusive_preds is not universe polymorphic
Arguments sum_split_exhaustive_mutually_exclusive_preds I r%seq_scope P (F Q R _ _)%function_scope
sum_split_exhaustive_mutually_exclusive_preds is opaque
Expands to: Constant prosa.util.sum.sum_split_exhaustive_mutually_exclusive_preds
Declared in library prosa.util.sum, line 59, characters 10-55
sum_split_exhaustive_mutually_exclusive_preds
     : forall (I : eqType) (r : seq (Equality.sort I)) (P : pred (Equality.sort I))
         (F : Equality.sort I -> nat) (Q R : Equality.sort I -> bool),
       (forall x : Equality.sort I, P x = Q x || R x) ->
       (forall x : Equality.sort I, is_true (~~ (Q x && R x))) ->
       @bigop.bigop.body nat (Equality.sort I) 0 r
         (fun r0 : Equality.sort I => @bigop.BigBody nat (Equality.sort I) r0 addn (P r0) (F r0)) =
       @bigop.bigop.body nat (Equality.sort I) 0 r
         (fun r0 : Equality.sort I => @bigop.BigBody nat (Equality.sort I) r0 addn (Q r0) (F r0)) +
       @bigop.bigop.body nat (Equality.sort I) 0 r
         (fun r0 : Equality.sort I => @bigop.BigBody nat (Equality.sort I) r0 addn (R r0) (F r0))
```

## Lean

```lean
@Prosa.Util.Sum.sum_split_exhaustive_mutually_exclusive_preds : ∀ {I : Type u_1} [DecidableEq I] (r : List I)
  (P : I → Bool) (F : I → ℕ) (Q R : I → Bool),
  (∀ (x : I), P x = (Q x || R x)) →
    (∀ (x : I), (!decide ((Q x && R x) = true)) = true) →
      Prosa.Util.Sum.sumFiltered r P F = Prosa.Util.Sum.sumFiltered r Q F + Prosa.Util.Sum.sumFiltered r R F
```

## Lean, imported into Rocq

```coq
Prosa_Util_Sum_sum_split_exhaustive_mutually_exclusive_preds
     : forall I : Type,
       ImportedSumSequence.DecidableEq I ->
       forall (r : ImportedSumSequence.List I) (P : I -> ImportedSumSequence.Bool) 
         (F : I -> Nat) (Q R : I -> ImportedSumSequence.Bool),
       (forall x : I, @eq ImportedSumSequence.Bool (P x) (Bool_or (Q x) (R x))) ->
       (forall x : I,
        @eq ImportedSumSequence.Bool
          (Bool_not
             (ImportedSumSequence.Decidable_decide
                (@eq ImportedSumSequence.Bool (ImportedSumSequence.Bool_and (Q x) (R x))
                   ImportedSumSequence.Bool_true)
                (instDecidableEqBool (ImportedSumSequence.Bool_and (Q x) (R x)) ImportedSumSequence.Bool_true)))
          ImportedSumSequence.Bool_true) ->
       @eq Nat (Prosa_Util_Sum_sumFiltered I r P F)
         (ImportedSumSequence.HAdd_hAdd_inst7 Nat Nat Nat
            (ImportedSumSequence.instHAdd_inst1 Nat ImportedSumSequence.instAddNat)
            (Prosa_Util_Sum_sumFiltered I r Q F) (Prosa_Util_Sum_sumFiltered I r R F))
```
