# `nonnil_last`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.list.nonnil_last`
- Lean: `Prosa.Util.List.nonnil_last`
- Certificate: `nonnil_last_statement_certificate`

## Official Rocq

```coq
nonnil_last :
forall {X : eqType} (xs : seq (Equality.sort X)) (d1 d2 : Equality.sort X),
is_true (xs != [::]) -> @last (Equality.sort X) d1 xs = @last (Equality.sort X) d2 xs

nonnil_last is not universe polymorphic
Arguments nonnil_last {X} xs%seq_scope d1 d2 _
nonnil_last is opaque
Expands to: Constant prosa.util.list.nonnil_last
Declared in library prosa.util.list, line 542, characters 6-17
@nonnil_last
     : forall (X : eqType) (xs : seq (Equality.sort X)) (d1 d2 : Equality.sort X),
       is_true (xs != [::]) -> @last (Equality.sort X) d1 xs = @last (Equality.sort X) d2 xs
```

## Lean

```lean
@Prosa.Util.List.nonnil_last : ∀ {X : Type u_1} [DecidableEq X] (xs : List X) (d1 d2 : X),
  xs ≠ [] → xs.getLastD d1 = xs.getLastD d2
```

## Lean, imported into Rocq

```coq
Prosa_Util_List_nonnil_last
     : forall X : Type,
       DecidableEq X ->
       forall (xs : List X) (d1 d2 : X),
       Ne (List X) xs (List_nil X) -> @eq X (List_getLastD X xs d1) (List_getLastD X xs d2)
```
