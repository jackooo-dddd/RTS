# `big_pred1_seq`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.bigop.big_pred1_seq`
- Lean: `Prosa.Util.Bigop.big_pred1_seq`
- Certificate: `big_pred1_seq_statement_certificate`

## Official Rocq

```coq
big_pred1_seq :
forall [R : Type] [idx : R] [op : Monoid.law idx] [X : eqType] [P : pred (Equality.sort X)]
  [F : Equality.sort X -> R] (xs : seq (Equality.sort X)) (i : Equality.sort X),
is_true (i \in xs) ->
is_true (@uniq X xs) ->
P =1 pred_of_simpl (@pred1 X i) -> \big[@Monoid.Law.sort R idx op/idx]_(j <- xs | P j) F j = F i

big_pred1_seq is not universe polymorphic
Arguments big_pred1_seq [R]%type_scope [idx op X P] [F]%function_scope xs%seq_scope i _ _ _
big_pred1_seq is opaque
Expands to: Constant prosa.util.bigop.big_pred1_seq
Declared in library prosa.util.bigop, line 7, characters 6-19
big_pred1_seq
     : forall (R : Type) (idx : R) (op : Monoid.law idx) (X : eqType) (P : pred (Equality.sort X))
         (F : Equality.sort X -> R) (xs : seq (Equality.sort X)) (i : Equality.sort X),
       is_true (i \in xs) ->
       is_true (@uniq X xs) ->
       P =1 pred_of_simpl (@pred1 X i) -> \big[@Monoid.Law.sort R idx op/idx]_(j <- xs | P j) F j = F i
```

## Lean

```lean
@Prosa.Util.Bigop.big_pred1_seq : ∀ {R : Type u_1} {idx : R} {op : R → R → R},
  (∀ (x y z : R), op x (op y z) = op (op x y) z) →
    (∀ (x : R), op idx x = x) →
      (∀ (x : R), op x idx = x) →
        ∀ {X : Type u_2} [inst : DecidableEq X] {P : X → Bool} {F : X → R} (xs : List X) (i : X),
          i ∈ xs → xs.Nodup → (∀ (x : X), P x = decide (x = i)) → Prosa.Util.Bigop.bigSeq idx op P F xs = F i
```

## Lean, imported into Rocq

```coq
Prosa_Util_Bigop_big_pred1_seq
     : forall (R : Type) (idx : R) (op : R -> R -> R),
       (forall x y z : R, @eq R (op x (op y z)) (op (op x y) z)) ->
       (forall x : R, @eq R (op idx x) x) ->
       (forall x : R, @eq R (op x idx) x) ->
       forall (X : Type) (inst_52 : DecidableEq X)
         (P : X -> Bool) (F : X -> R) (xs : List X) (i : X),
       Membership_mem X (List X) (List_instMembership X) xs i ->
       List_Nodup X xs ->
       (forall x : X,
        @eq Bool (P x)
          (Decidable_decide (@eq X x i) (inst_52 x i))) ->
       @eq R (Prosa_Util_Bigop_bigSeq R X idx op P F xs) (F i)
```
