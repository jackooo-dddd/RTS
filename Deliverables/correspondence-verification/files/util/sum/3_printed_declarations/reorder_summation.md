# `reorder_summation`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.sum.reorder_summation`
- Lean: `Prosa.Util.Sum.reorder_summation`
- Certificate: `reorder_summation_statement_certificate`

## Official Rocq

```coq
reorder_summation :
forall (X Y : eqType) (x_to_y : Equality.sort X -> Equality.sort Y) (f : Equality.sort X -> nat)
  (P : pred (Equality.sort X)) (xs : seq (Equality.sort X)) (ys : seq (Equality.sort Y)),
(forall x : Equality.sort X, is_true (x \in xs) -> is_true (P x) -> is_true (x_to_y x \in ys)) ->
forall y' : Equality.sort Y,
is_true
  (@bigop.bigop.body nat (Equality.sort X) 0 xs
     (fun x : Equality.sort X => @bigop.BigBody nat (Equality.sort X) x addn (P x && (x_to_y x != y')) (f x)) <=
   @bigop.bigop.body nat (Equality.sort Y) 0 ys
     (fun y : Equality.sort Y =>
      @bigop.BigBody nat (Equality.sort Y) y addn (y != y')
        ((fun y0 : Equality.sort Y =>
          @bigop.bigop.body nat (Equality.sort X) 0 xs
            (fun x : Equality.sort X =>
             @bigop.BigBody nat (Equality.sort X) x addn (P x && (x_to_y x == y0)) (f x)))
           y)))

reorder_summation is not universe polymorphic
Arguments reorder_summation X Y (x_to_y f)%function_scope P (xs ys)%seq_scope
  H_no_partition_missing%function_scope y'
reorder_summation is opaque
Expands to: Constant prosa.util.sum.reorder_summation
Declared in library prosa.util.sum, line 354, characters 8-25
reorder_summation
     : forall (X Y : eqType) (x_to_y : Equality.sort X -> Equality.sort Y) (f : Equality.sort X -> nat)
         (P : pred (Equality.sort X)) (xs : seq (Equality.sort X)) (ys : seq (Equality.sort Y)),
       (forall x : Equality.sort X, is_true (x \in xs) -> is_true (P x) -> is_true (x_to_y x \in ys)) ->
       forall y' : Equality.sort Y,
       is_true
         (@bigop.bigop.body nat (Equality.sort X) 0 xs
            (fun x : Equality.sort X =>
             @bigop.BigBody nat (Equality.sort X) x addn (P x && (x_to_y x != y')) (f x)) <=
          @bigop.bigop.body nat (Equality.sort Y) 0 ys
            (fun y : Equality.sort Y =>
             @bigop.BigBody nat (Equality.sort Y) y addn (y != y')
               (@bigop.bigop.body nat (Equality.sort X) 0 xs
                  (fun x : Equality.sort X =>
                   @bigop.BigBody nat (Equality.sort X) x addn (P x && (x_to_y x == y)) (f x)))))
```

## Lean

```lean
@Prosa.Util.Sum.reorder_summation : ∀ {X : Type u_1} {Y : Type u_2} [DecidableEq X] [inst : DecidableEq Y]
  (xToY : X → Y) (f : X → ℕ) (P : X → Bool) (xs : List X) (ys : List Y),
  (∀ x ∈ xs, P x = true → xToY x ∈ ys) →
    ∀ (y' : Y),
      Prosa.Util.Sum.sumFiltered xs (fun x => P x && decide (xToY x ≠ y')) f ≤
        Prosa.Util.Sum.sumOverPartitions xToY f P xs (List.filter (fun y => decide (y ≠ y')) ys)
```

## Lean, imported into Rocq

```coq
Prosa_Util_Sum_reorder_summation
     : forall X Y : Type,
       ImportedSumSequence.DecidableEq X ->
       forall (inst_7 : ImportedSumSequence.DecidableEq Y)
         (xToY : X -> Y) (f : X -> Nat) (P : X -> ImportedSumSequence.Bool) (xs : ImportedSumSequence.List X)
         (ys : ImportedSumSequence.List Y),
       (forall x : X,
        Membership_mem X (ImportedSumSequence.List X) (List_instMembership X) xs x ->
        @eq ImportedSumSequence.Bool (P x) ImportedSumSequence.Bool_true ->
        Membership_mem Y (ImportedSumSequence.List Y) (List_instMembership Y) ys (xToY x)) ->
       forall y' : Y,
       ImportedSumSequence.LE_le_inst1 Nat ImportedSumSequence.instLENat
         (Prosa_Util_Sum_sumFiltered X xs
            (fun x : X =>
             ImportedSumSequence.Bool_and (P x)
               (ImportedSumSequence.Decidable_decide (Ne Y (xToY x) y')
                  (instDecidableNot (@eq Y (xToY x) y')
                     (inst_7 (xToY x) y'))))
            f)
         (Prosa_Util_Sum_sumOverPartitions X Y inst_7 xToY f P
            xs
            (List_filter Y
               (fun y : Y =>
                ImportedSumSequence.Decidable_decide (Ne Y y y')
                  (instDecidableNot (@eq Y y y') (inst_7 y y')))
               ys))
```
