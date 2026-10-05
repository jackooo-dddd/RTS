# `rem_in`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.list.rem_in`
- Lean: `Prosa.Util.List.rem_in`
- Certificate: `rem_in_statement_certificate`

## Official Rocq

```coq
rem_in :
forall {X : eqType} (x y : Equality.sort X) (xs : seq (Equality.sort X)),
is_true (x \in @rem X y xs) -> is_true (x \in xs)

rem_in is not universe polymorphic
Arguments rem_in {X} x y xs%seq_scope _
rem_in is opaque
Expands to: Constant prosa.util.list.rem_in
Declared in library prosa.util.list, line 224, characters 6-12
@rem_in
     : forall (X : eqType) (x y : Equality.sort X) (xs : seq (Equality.sort X)),
       is_true (x \in @rem X y xs) -> is_true (x \in xs)
```

## Lean

```lean
@Prosa.Util.List.rem_in : ∀ {T : Type u_1} [inst : DecidableEq T] (x y : T) (xs : List T), x ∈ xs.erase y → x ∈ xs
```

## Lean, imported into Rocq

```coq
Prosa_Util_List_rem_in
     : forall (T : Type) (inst_3 : DecidableEq T) 
         (x y : T) (xs : List T),
       Membership_mem T (List T) (List_instMembership T)
         (List_erase T (instBEqOfDecidableEq T inst_3) xs y) x ->
       Membership_mem T (List T) (List_instMembership T) xs x
```
