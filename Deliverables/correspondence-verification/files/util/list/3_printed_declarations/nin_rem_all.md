# `nin_rem_all`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.list.nin_rem_all`
- Lean: `Prosa.Util.List.nin_rem_all`
- Certificate: `nin_rem_all_statement_certificate`

## Official Rocq

```coq
nin_rem_all :
forall {X : eqType} (x : Equality.sort X) (xs : seq (Equality.sort X)), ~ is_true (x \in @rem_all X x xs)

nin_rem_all is not universe polymorphic
Arguments nin_rem_all {X} x xs%seq_scope _
nin_rem_all is opaque
Expands to: Constant prosa.util.list.nin_rem_all
Declared in library prosa.util.list, line 587, characters 6-17
@nin_rem_all
     : forall (X : eqType) (x : Equality.sort X) (xs : seq (Equality.sort X)),
       ~ is_true (x \in @rem_all X x xs)
```

## Lean

```lean
@Prosa.Util.List.nin_rem_all : ∀ {T : Type u_1} [inst : DecidableEq T] (x : T) (xs : List T),
  ¬x ∈ Prosa.Util.List.rem_all x xs
```

## Lean, imported into Rocq

```coq
Prosa_Util_List_nin_rem_all
     : forall (T : Type) (inst_3 : DecidableEq T) 
         (x : T) (xs : List T),
       Not
         (Membership_mem T (List T) (List_instMembership T)
            (Prosa_Util_List_rem_all T inst_3 x xs) x)
```
