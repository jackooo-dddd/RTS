# `eq_ind_in_seq`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.list.eq_ind_in_seq`
- Lean: `Prosa.Util.List.eq_ind_in_seq`
- Certificate: `eq_ind_in_seq_statement_certificate`

## Official Rocq

```coq
eq_ind_in_seq :
forall {X : eqType} (a b : Equality.sort X) (xs : seq (Equality.sort X)),
@index X a xs = @index X b xs -> is_true (a \in xs) -> is_true (b \in xs) -> a = b

eq_ind_in_seq is not universe polymorphic
Arguments eq_ind_in_seq {X} a b xs%seq_scope _ _ _
eq_ind_in_seq is opaque
Expands to: Constant prosa.util.list.eq_ind_in_seq
Declared in library prosa.util.list, line 437, characters 6-19
@eq_ind_in_seq
     : forall (X : eqType) (a b : Equality.sort X) (xs : seq (Equality.sort X)),
       @index X a xs = @index X b xs -> is_true (a \in xs) -> is_true (b \in xs) -> a = b
```

## Lean

```lean
@Prosa.Util.List.eq_ind_in_seq : ∀ {X : Type u_1} [inst : DecidableEq X] (a b : X) (xs : List X),
  List.idxOf a xs = List.idxOf b xs → a ∈ xs → b ∈ xs → a = b
```

## Lean, imported into Rocq

```coq
Prosa_Util_List_eq_ind_in_seq
     : forall (X : Type) (inst_3 : DecidableEq X) 
         (a b : X) (xs : List X),
       @eq Nat
         (List_idxOf X (instBEqOfDecidableEq X inst_3) a xs)
         (List_idxOf X (instBEqOfDecidableEq X inst_3) b xs) ->
       Membership_mem X (List X) (List_instMembership X) xs a ->
       Membership_mem X (List X) (List_instMembership X) xs b -> @eq X a b
```
