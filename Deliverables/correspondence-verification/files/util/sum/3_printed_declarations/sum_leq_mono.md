# `sum_leq_mono`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.sum.sum_leq_mono`
- Lean: `Prosa.Util.Sum.sum_leq_mono`
- Certificate: `sum_leq_mono_statement_certificate`

## Official Rocq

```coq
sum_leq_mono :
forall (I : eqType) (P : pred (Equality.sort I)) (F : Equality.sort I -> nat -> nat)
  (r : seq (Equality.sort I)),
(forall i : Equality.sort I, is_true (i \in r) -> @monotone nat leq (F i)) ->
@monotone nat leq
  (fun x : nat =>
   @bigop.bigop.body nat (Equality.sort I) 0 r
     (fun i : Equality.sort I => @bigop.BigBody nat (Equality.sort I) i addn (P i) (F i x)))

sum_leq_mono is not universe polymorphic
Arguments sum_leq_mono I P F%function_scope r%seq_scope H_mono%function_scope x y _
sum_leq_mono is opaque
Expands to: Constant prosa.util.sum.sum_leq_mono
Declared in library prosa.util.sum, line 433, characters 8-20
sum_leq_mono
     : forall (I : eqType) (P : pred (Equality.sort I)) (F : Equality.sort I -> nat -> nat)
         (r : seq (Equality.sort I)),
       (forall i : Equality.sort I, is_true (i \in r) -> @monotone nat leq (F i)) ->
       @monotone nat leq
         (fun x : nat =>
          @bigop.bigop.body nat (Equality.sort I) 0 r
            (fun i : Equality.sort I => @bigop.BigBody nat (Equality.sort I) i addn (P i) (F i x)))
```

## Lean

```lean
@Prosa.Util.Sum.sum_leq_mono : ∀ {I : Type u_1} [DecidableEq I] (P : I → Bool) (F : I → ℕ → ℕ) (r : List I),
  (∀ i ∈ r, Prosa.Util.Rel.monotone (fun x y => decide (x ≤ y)) (F i)) →
    Prosa.Util.Rel.monotone (fun x y => decide (x ≤ y)) fun x => Prosa.Util.Sum.sumFiltered r P fun i => F i x
```

## Lean, imported into Rocq

```coq
Prosa_Util_Sum_sum_leq_mono
     : forall I : Type,
       ImportedSumSequence.DecidableEq I ->
       forall (P : I -> ImportedSumSequence.Bool) (F : I -> Nat -> Nat) (r : ImportedSumSequence.List I),
       (forall i : I,
        Membership_mem I (ImportedSumSequence.List I) (List_instMembership I) r i ->
        Prosa_Util_Rel_monotone_inst1 Nat
          (fun x y : Nat =>
           ImportedSumSequence.Decidable_decide
             (ImportedSumSequence.LE_le_inst1 Nat ImportedSumSequence.instLENat x y) 
             (Nat_decLe x y))
          (F i)) ->
       Prosa_Util_Rel_monotone_inst1 Nat
         (fun x y : Nat =>
          ImportedSumSequence.Decidable_decide
            (ImportedSumSequence.LE_le_inst1 Nat ImportedSumSequence.instLENat x y) 
            (Nat_decLe x y))
         (fun x : Nat => Prosa_Util_Sum_sumFiltered I r P (fun i : I => F i x))
```
