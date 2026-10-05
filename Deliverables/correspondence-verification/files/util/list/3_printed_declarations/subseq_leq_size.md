# `subseq_leq_size`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.list.subseq_leq_size`
- Lean: `Prosa.Util.List.subseq_leq_size`
- Certificate: `subseq_leq_size_statement_certificate`

## Official Rocq

```coq
subseq_leq_size :
forall {X : eqType} (xs ys : seq (Equality.sort X)),
is_true (@uniq X xs) ->
(forall x : Equality.sort X, is_true (x \in xs) -> is_true (x \in ys)) ->
is_true (@size (Equality.sort X) xs <= @size (Equality.sort X) ys)

subseq_leq_size is not universe polymorphic
Arguments subseq_leq_size {X} (xs ys)%seq_scope _ _%function_scope
subseq_leq_size is opaque
Expands to: Constant prosa.util.list.subseq_leq_size
Declared in library prosa.util.list, line 356, characters 6-21
@subseq_leq_size
     : forall (X : eqType) (xs ys : seq (Equality.sort X)),
       is_true (@uniq X xs) ->
       (forall x : Equality.sort X, is_true (x \in xs) -> is_true (x \in ys)) ->
       is_true (@size (Equality.sort X) xs <= @size (Equality.sort X) ys)
```

## Lean

```lean
@Prosa.Util.List.subseq_leq_size : ∀ {X : Type u_1} [DecidableEq X] (xs ys : List X),
  xs.Nodup → (∀ (x : X), x ∈ xs → x ∈ ys) → xs.length ≤ ys.length
```

## Lean, imported into Rocq

```coq
Prosa_Util_List_subseq_leq_size
     : forall X : Type,
       DecidableEq X ->
       forall xs ys : List X,
       List_Nodup X xs ->
       (forall x : X,
        Membership_mem X (List X) (List_instMembership X) xs x ->
        Membership_mem X (List X) (List_instMembership X) ys x) ->
       LE_le_inst1 Nat instLENat (List_length X xs) (List_length X ys)
```
