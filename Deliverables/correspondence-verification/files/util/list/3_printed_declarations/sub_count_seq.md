# `sub_count_seq`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.list.sub_count_seq`
- Lean: `Prosa.Util.List.sub_count_seq`
- Certificate: `sub_count_seq_statement_certificate`

## Official Rocq

```coq
sub_count_seq :
forall {X : eqType} (f g : pred (Equality.sort X)) (xs : seq (Equality.sort X)),
{in xs, forall x : Equality.sort X, is_true (f x) -> is_true (g x)} ->
is_true (@count (Equality.sort X) f xs <= @count (Equality.sort X) g xs)

sub_count_seq is not universe polymorphic
Arguments sub_count_seq {X} f g xs%seq_scope _
sub_count_seq is opaque
Expands to: Constant prosa.util.list.sub_count_seq
Declared in library prosa.util.list, line 844, characters 6-19
@sub_count_seq
     : forall (X : eqType) (f g : pred (Equality.sort X)) (xs : seq (Equality.sort X)),
       {in xs, forall x : Equality.sort X, is_true (f x) -> is_true (g x)} ->
       is_true (@count (Equality.sort X) f xs <= @count (Equality.sort X) g xs)
```

## Lean

```lean
@Prosa.Util.List.sub_count_seq : ∀ {X : Type u_1} [DecidableEq X] (f g : X → Bool) (xs : List X),
  (∀ (x : X), x ∈ xs → f x = true → g x = true) → List.countP f xs ≤ List.countP g xs
```

## Lean, imported into Rocq

```coq
Prosa_Util_List_sub_count_seq
     : forall X : Type,
       DecidableEq X ->
       forall (f g : X -> Bool) (xs : List X),
       (forall x : X,
        Membership_mem X (List X) (List_instMembership X) xs x ->
        @eq Bool (f x) Bool_true -> @eq Bool (g x) Bool_true) ->
       LE_le_inst1 Nat instLENat (List_countP X f xs) (List_countP X g xs)
```
