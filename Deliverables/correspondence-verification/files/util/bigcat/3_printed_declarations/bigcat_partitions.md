# `bigcat_partitions`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.bigcat.bigcat_partitions`
- Lean: `Prosa.Util.Bigcat.bigcat_partitions`
- Certificate: `bigcat_partitions_statement_certificate`

## Official Rocq

```coq
bigcat_partitions :
forall (X Y : eqType) (xs : seq (Equality.sort X)) (ys : seq (Equality.sort Y)) (P : pred (Equality.sort X))
  (x_to_y : Equality.sort X -> Equality.sort Y),
(forall x : Equality.sort X, is_true (x \in xs) -> is_true (P x) -> is_true (x_to_y x \in ys)) ->
forall j : Equality.sort X,
(j \in [seq x <- xs | P x]) =
(j
   \in @bigop.bigop.body (seq (Equality.sort X)) (Equality.sort Y) [::] ys
         (fun y : Equality.sort Y =>
          @bigop.BigBody (seq (Equality.sort X)) (Equality.sort Y) y (@cat (Equality.sort X)) true
            ((fun y0 : Equality.sort Y => [seq x <- xs | P x & x_to_y x == y0]) y)))

bigcat_partitions is not universe polymorphic
Arguments bigcat_partitions X Y (xs ys)%seq_scope P (x_to_y H_no_partition_missing)%function_scope j
bigcat_partitions is opaque
Expands to: Constant prosa.util.bigcat.bigcat_partitions
Declared in library prosa.util.bigcat, line 330, characters 8-25
bigcat_partitions
     : forall (X Y : eqType) (xs : seq (Equality.sort X)) (ys : seq (Equality.sort Y))
         (P : pred (Equality.sort X)) (x_to_y : Equality.sort X -> Equality.sort Y),
       (forall x : Equality.sort X, is_true (x \in xs) -> is_true (P x) -> is_true (x_to_y x \in ys)) ->
       forall j : Equality.sort X,
       (j \in [seq x <- xs | P x]) =
       (j
          \in @bigop.bigop.body (seq (Equality.sort X)) (Equality.sort Y) [::] ys
                (fun y : Equality.sort Y =>
                 @bigop.BigBody (seq (Equality.sort X)) (Equality.sort Y) y (@cat (Equality.sort X)) true
                   [seq x <- xs | P x & x_to_y x == y]))
```

## Lean

```lean
@Prosa.Util.Bigcat.bigcat_partitions : ∀ {X : Type u_1} {Y : Type u_2} [inst : DecidableEq X] [inst_1 : DecidableEq Y]
  (xs : List X) (ys : List Y) (P : X → Bool) (xToY : X → Y),
  (∀ x ∈ xs, P x = true → xToY x ∈ ys) →
    ∀ (j : X),
      decide (j ∈ List.filter P xs) =
        decide (j ∈ Prosa.Util.Bigcat.bigCatSeqAll ys fun y => List.filter (fun x => P x && decide (xToY x = y)) xs)
```

## Lean, imported into Rocq

```coq
Prosa_Util_Bigcat_bigcat_partitions
     : forall (X Y : Type) (inst_4 : DecidableEq X)
         (inst_7 : DecidableEq Y) 
         (xs : List X) (ys : List Y) (P : X -> Bool) (xToY : X -> Y),
       (forall x : X,
        Membership_mem X (List X) (List_instMembership X) xs x ->
        @eq Bool (P x) Bool_true -> Membership_mem Y (List Y) (List_instMembership Y) ys (xToY x)) ->
       forall j : X,
       @eq Bool
         (Decidable_decide (Membership_mem X (List X) (List_instMembership X) (List_filter X P xs) j)
            (List_instDecidableMemOfLawfulBEq X
               (instBEqOfDecidableEq X inst_4)
               (instLawfulBEq X inst_4) j
               (List_filter X P xs)))
         (Decidable_decide
            (Membership_mem X (List X) (List_instMembership X)
               (Prosa_Util_Bigcat_bigCatSeqAll Y X ys
                  (fun y : Y =>
                   List_filter X
                     (fun x : X =>
                      Bool_and (P x)
                        (Decidable_decide (@eq Y (xToY x) y)
                           (inst_7 (xToY x) y)))
                     xs))
               j)
            (List_instDecidableMemOfLawfulBEq X
               (instBEqOfDecidableEq X inst_4)
               (instLawfulBEq X inst_4) j
               (Prosa_Util_Bigcat_bigCatSeqAll Y X ys
                  (fun y : Y =>
                   List_filter X
                     (fun x : X =>
                      Bool_and (P x)
                        (Decidable_decide (@eq Y (xToY x) y)
                           (inst_7 (xToY x) y)))
                     xs))))
```
