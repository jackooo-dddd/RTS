# `exists_two`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.list.exists_two`
- Lean: `Prosa.Util.List.exists_two`
- Certificate: `exists_two_statement_certificate`

## Official Rocq

```coq
exists_two :
forall {X : eqType} (xs : seq (Equality.sort X)),
is_true (1 < @size (Equality.sort X) xs) ->
is_true (@uniq X xs) -> exists a b : Equality.sort X, a <> b /\ is_true (a \in xs) /\ is_true (b \in xs)

exists_two is not universe polymorphic
Arguments exists_two {X} xs%seq_scope _ _
exists_two is opaque
Expands to: Constant prosa.util.list.exists_two
Declared in library prosa.util.list, line 463, characters 6-16
@exists_two
     : forall (X : eqType) (xs : seq (Equality.sort X)),
       is_true (1 < @size (Equality.sort X) xs) ->
       is_true (@uniq X xs) ->
       exists a b : Equality.sort X, a <> b /\ is_true (a \in xs) /\ is_true (b \in xs)
```

## Lean

```lean
@Prosa.Util.List.exists_two : ∀ {X : Type u_1} [DecidableEq X] (xs : List X),
  1 < xs.length → xs.Nodup → ∃ a b, a ≠ b ∧ a ∈ xs ∧ b ∈ xs
```

## Lean, imported into Rocq

```coq
Prosa_Util_List_exists_two
     : forall X : Type,
       DecidableEq X ->
       forall xs : List X,
       LT_lt_inst1 Nat instLTNat (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1)) (List_length X xs) ->
       List_Nodup X xs ->
       Exists X
         (fun a : X =>
          Exists X
            (fun b : X =>
             And (Ne X a b)
               (And (Membership_mem X (List X) (List_instMembership X) xs a)
                  (Membership_mem X (List X) (List_instMembership X) xs b))))
```
