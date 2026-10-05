# `in_neq_impl_rem_in`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.list.in_neq_impl_rem_in`
- Lean: `Prosa.Util.List.in_neq_impl_rem_in`
- Certificate: `in_neq_impl_rem_in_statement_certificate`

## Official Rocq

```coq
in_neq_impl_rem_in :
forall {X : eqType} (x y : Equality.sort X) (xs : seq (Equality.sort X)),
is_true (x \in xs) -> is_true (x != y) -> is_true (x \in @rem X y xs)

in_neq_impl_rem_in is not universe polymorphic
Arguments in_neq_impl_rem_in {X} x y xs%seq_scope _ _
in_neq_impl_rem_in is opaque
Expands to: Constant prosa.util.list.in_neq_impl_rem_in
Declared in library prosa.util.list, line 242, characters 6-24
@in_neq_impl_rem_in
     : forall (X : eqType) (x y : Equality.sort X) (xs : seq (Equality.sort X)),
       is_true (x \in xs) -> is_true (x != y) -> is_true (x \in @rem X y xs)
```

## Lean

```lean
@Prosa.Util.List.in_neq_impl_rem_in : ∀ {T : Type u_1} [inst : DecidableEq T] (x y : T) (xs : List T),
  x ∈ xs → x ≠ y → x ∈ xs.erase y
```

## Lean, imported into Rocq

```coq
Prosa_Util_List_in_neq_impl_rem_in
     : forall (T : Type) (inst_3 : DecidableEq T) 
         (x y : T) (xs : List T),
       Membership_mem T (List T) (List_instMembership T) xs x ->
       Ne T x y ->
       Membership_mem T (List T) (List_instMembership T)
         (List_erase T (instBEqOfDecidableEq T inst_3) xs y) x
```
