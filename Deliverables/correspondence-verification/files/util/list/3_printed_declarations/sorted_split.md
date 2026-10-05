# `sorted_split`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.list.sorted_split`
- Lean: `Prosa.Util.List.sorted_split`
- Certificate: `sorted_split_statement_certificate`

## Official Rocq

```coq
sorted_split :
forall {X : eqType} (xs : seq (Equality.sort X)) (P : Equality.sort X -> bool) (f : Equality.sort X -> nat)
  (t : nat),
is_true (@path.sorted (Equality.sort X) (fun x y : Equality.sort X => f x <= f y) xs) ->

sorted_split is not universe polymorphic
Arguments sorted_split {X} xs%seq_scope (P f)%function_scope t%nat_scope _
sorted_split is opaque
Expands to: Constant prosa.util.list.sorted_split
Declared in library prosa.util.list, line 499, characters 6-18
@sorted_split
     : forall (X : eqType) (xs : seq (Equality.sort X)) (P : Equality.sort X -> bool)
         (f : Equality.sort X -> nat) (t : nat),
       is_true (@path.sorted (Equality.sort X) (fun x y : Equality.sort X => f x <= f y) xs) ->
       [seq x <- xs | P x] = [seq x <- xs | P x & f x <= t] ++ [seq x <- xs | P x & t < f x]
```

## Lean

```lean
@Prosa.Util.List.sorted_split : ∀ {X : Type u_1} [DecidableEq X] (xs : List X) (P : X → Bool) (f : X → ℕ) (t : ℕ),
  Prosa.Util.List.boolSorted (fun x y => decide (f x ≤ f y)) xs →
    List.filter P xs =
      List.filter (fun x => P x && decide (f x ≤ t)) xs ++ List.filter (fun x => P x && decide (t < f x)) xs
```

## Lean, imported into Rocq

```coq
Prosa_Util_List_sorted_split
     : forall X : Type,
       DecidableEq X ->
       forall (xs : List X) (P : X -> Bool) (f : X -> Nat) (t : Nat),
       Prosa_Util_List_boolSorted X
         (fun x y : X => Decidable_decide (LE_le_inst1 Nat instLENat (f x) (f y)) (Nat_decLe (f x) (f y))) xs ->
       @eq (List X) (List_filter X P xs)
         (HAppend_hAppend (List X) (List X) (List X) (instHAppendOfAppend (List X) (List_instAppend X))
            (List_filter X
               (fun x : X =>
                Bool_and (P x) (Decidable_decide (LE_le_inst1 Nat instLENat (f x) t) (Nat_decLe (f x) t)))
               xs)
            (List_filter X
               (fun x : X =>
                Bool_and (P x) (Decidable_decide (LT_lt_inst1 Nat instLTNat t (f x)) (Nat_decLt t (f x))))
               xs))
```
