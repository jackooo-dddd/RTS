# `default_or_in`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.list.default_or_in`
- Lean: `Prosa.Util.List.default_or_in`
- Certificate: `default_or_in_statement_certificate`

## Official Rocq

```coq
default_or_in :
forall {X : eqType} (n : nat) (d : Equality.sort X) (xs : seq (Equality.sort X)),
@nth (Equality.sort X) d xs n = d \/ is_true (@nth (Equality.sort X) d xs n \in xs)

default_or_in is not universe polymorphic
Arguments default_or_in {X} n%nat_scope d xs%seq_scope
default_or_in is opaque
Expands to: Constant prosa.util.list.default_or_in
Declared in library prosa.util.list, line 452, characters 6-19
@default_or_in
     : forall (X : eqType) (n : nat) (d : Equality.sort X) (xs : seq (Equality.sort X)),
       @nth (Equality.sort X) d xs n = d \/ is_true (@nth (Equality.sort X) d xs n \in xs)
```

## Lean

```lean
@Prosa.Util.List.default_or_in : ∀ {X : Type u_1} [DecidableEq X] (n : ℕ) (d : X) (xs : List X),
  xs.getD n d = d ∨ xs.getD n d ∈ xs
```

## Lean, imported into Rocq

```coq
Prosa_Util_List_default_or_in
     : forall X : Type,
       DecidableEq X ->
       forall (n : Nat) (d : X) (xs : List X),
       Or (@eq X (List_getD X xs n d) d)
         (Membership_mem X (List X) (List_instMembership X) xs (List_getD X xs n d))
```
