# `sorted_cat`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.list.sorted_cat`
- Lean: `Prosa.Util.List.sorted_cat`
- Certificate: `sorted_cat_statement_certificate`

## Official Rocq

```coq
sorted_cat :
forall {X : eqType} {R : rel (Equality.sort X)} (xs1 xs2 : seq (Equality.sort X)),
@transitive (Equality.sort X) R ->
is_true (@path.sorted (Equality.sort X) R (xs1 ++ xs2)) ->
is_true (@path.sorted (Equality.sort X) R xs1) /\ is_true (@path.sorted (Equality.sort X) R xs2)

sorted_cat is not universe polymorphic
Arguments sorted_cat {X R} (xs1 xs2)%seq_scope _ _
sorted_cat is opaque
Expands to: Constant prosa.util.list.sorted_cat
Declared in library prosa.util.list, line 522, characters 6-16
@sorted_cat
     : forall (X : eqType) (R : rel (Equality.sort X)) (xs1 xs2 : seq (Equality.sort X)),
       @transitive (Equality.sort X) R ->
       is_true (@path.sorted (Equality.sort X) R (xs1 ++ xs2)) ->
       is_true (@path.sorted (Equality.sort X) R xs1) /\ is_true (@path.sorted (Equality.sort X) R xs2)
```

## Lean

```lean
@Prosa.Util.List.sorted_cat : ∀ {X : Type u_1} [DecidableEq X] (R : X → X → Bool) (xs1 xs2 : List X),
  (∀ (x y z : X), R x y = true → R y z = true → R x z = true) →
    Prosa.Util.List.boolSorted R (xs1 ++ xs2) → Prosa.Util.List.boolSorted R xs1 ∧ Prosa.Util.List.boolSorted R xs2
```

## Lean, imported into Rocq

```coq
Prosa_Util_List_sorted_cat
     : forall X : Type,
       DecidableEq X ->
       forall (R : X -> X -> Bool) (xs1 xs2 : List X),
       (forall x y z : X,
        @eq Bool (R x y) Bool_true -> @eq Bool (R y z) Bool_true -> @eq Bool (R x z) Bool_true) ->
       Prosa_Util_List_boolSorted X R
         (HAppend_hAppend (List X) (List X) (List X) (instHAppendOfAppend (List X) (List_instAppend X)) xs1
            xs2) ->
       And (Prosa_Util_List_boolSorted X R xs1) (Prosa_Util_List_boolSorted X R xs2)
```
