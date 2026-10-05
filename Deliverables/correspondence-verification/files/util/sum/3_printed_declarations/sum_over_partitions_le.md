# `sum_over_partitions_le`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.sum.sum_over_partitions_le`
- Lean: `Prosa.Util.Sum.sum_over_partitions_le`
- Certificate: `sum_over_partitions_le_statement_certificate`

## Official Rocq

```coq
sum_over_partitions_le :
forall (X Y : eqType) (x_to_y : Equality.sort X -> Equality.sort Y) (f : Equality.sort X -> nat)
  (P : pred (Equality.sort X)) (xs : seq (Equality.sort X)) (ys : seq (Equality.sort Y)),
(forall x : Equality.sort X, is_true (x \in xs) -> is_true (P x) -> is_true (x_to_y x \in ys)) ->
is_true
  (@bigop.bigop.body nat (Equality.sort X) 0 xs
     (fun x : Equality.sort X => @bigop.BigBody nat (Equality.sort X) x addn (P x) (f x)) <=
   @bigop.bigop.body nat (Equality.sort Y) 0 ys
     (fun y : Equality.sort Y =>
      @bigop.BigBody nat (Equality.sort Y) y addn true
        ((fun y0 : Equality.sort Y =>
          @bigop.bigop.body nat (Equality.sort X) 0 xs
            (fun x : Equality.sort X =>
             @bigop.BigBody nat (Equality.sort X) x addn (P x && (x_to_y x == y0)) (f x)))
           y)))

sum_over_partitions_le is not universe polymorphic
Arguments sum_over_partitions_le X Y (x_to_y f)%function_scope P (xs ys)%seq_scope
  H_no_partition_missing%function_scope
sum_over_partitions_le is opaque
Expands to: Constant prosa.util.sum.sum_over_partitions_le
Declared in library prosa.util.sum, line 329, characters 8-30
sum_over_partitions_le
     : forall (X Y : eqType) (x_to_y : Equality.sort X -> Equality.sort Y) (f : Equality.sort X -> nat)
         (P : pred (Equality.sort X)) (xs : seq (Equality.sort X)) (ys : seq (Equality.sort Y)),
       (forall x : Equality.sort X, is_true (x \in xs) -> is_true (P x) -> is_true (x_to_y x \in ys)) ->
       is_true
         (@bigop.bigop.body nat (Equality.sort X) 0 xs
            (fun x : Equality.sort X => @bigop.BigBody nat (Equality.sort X) x addn (P x) (f x)) <=
          @bigop.bigop.body nat (Equality.sort Y) 0 ys
            (fun y : Equality.sort Y =>
             @bigop.BigBody nat (Equality.sort Y) y addn true
               (@bigop.bigop.body nat (Equality.sort X) 0 xs
                  (fun x : Equality.sort X =>
                   @bigop.BigBody nat (Equality.sort X) x addn (P x && (x_to_y x == y)) (f x)))))
```

## Lean

```lean
@Prosa.Util.Sum.sum_over_partitions_le : ∀ {X : Type u_1} {Y : Type u_2} [DecidableEq X] [inst : DecidableEq Y]
  (xToY : X → Y) (f : X → ℕ) (P : X → Bool) (xs : List X) (ys : List Y),
  (∀ x ∈ xs, P x = true → xToY x ∈ ys) →
    Prosa.Util.Sum.sumFiltered xs P f ≤ Prosa.Util.Sum.sumOverPartitions xToY f P xs ys
```

## Lean, imported into Rocq

```coq
Prosa_Util_Sum_sum_over_partitions_le
     : forall X Y : Type,
       ImportedSumSequence.DecidableEq X ->
       forall (inst_7 : ImportedSumSequence.DecidableEq Y)
         (xToY : X -> Y) (f : X -> Nat) (P : X -> ImportedSumSequence.Bool) (xs : ImportedSumSequence.List X)
         (ys : ImportedSumSequence.List Y),
       (forall x : X,
        Membership_mem X (ImportedSumSequence.List X) (List_instMembership X) xs x ->
        @eq ImportedSumSequence.Bool (P x) ImportedSumSequence.Bool_true ->
        Membership_mem Y (ImportedSumSequence.List Y) (List_instMembership Y) ys (xToY x)) ->
       ImportedSumSequence.LE_le_inst1 Nat ImportedSumSequence.instLENat
         (Prosa_Util_Sum_sumFiltered X xs P f)
         (Prosa_Util_Sum_sumOverPartitions X Y inst_7 xToY f P xs
            ys)
```
