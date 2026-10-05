# `in_rem_all`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.list.in_rem_all`
- Lean: `Prosa.Util.List.in_rem_all`
- Certificate: `in_rem_all_statement_certificate`

## Official Rocq

```coq
in_rem_all :
forall {X : eqType} (a x : Equality.sort X) (xs : seq (Equality.sort X)),
is_true (a \in @rem_all X x xs) -> is_true (a \in xs)

in_rem_all is not universe polymorphic
Arguments in_rem_all {X} a x xs%seq_scope _
in_rem_all is opaque
Expands to: Constant prosa.util.list.in_rem_all
Declared in library prosa.util.list, line 599, characters 6-16
@in_rem_all
     : forall (X : eqType) (a x : Equality.sort X) (xs : seq (Equality.sort X)),
       is_true (a \in @rem_all X x xs) -> is_true (a \in xs)
```

## Lean

```lean
@Prosa.Util.List.in_rem_all : ∀ {T : Type u_1} [inst : DecidableEq T] (a x : T) (xs : List T),
  a ∈ Prosa.Util.List.rem_all x xs → a ∈ xs
```

## Lean, imported into Rocq

```coq
Prosa_Util_List_in_rem_all
     : forall (T : Type) (inst_3 : DecidableEq T) 
         (a x : T) (xs : List T),
       Membership_mem T (List T) (List_instMembership T)
         (Prosa_Util_List_rem_all T inst_3 x xs) a ->
       Membership_mem T (List T) (List_instMembership T) xs a
```
