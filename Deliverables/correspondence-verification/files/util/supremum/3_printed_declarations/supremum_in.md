# `supremum_in`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.supremum.supremum_in`
- Lean: `Prosa.Util.Supremum.supremum_in`
- Certificate: `supremum_in_statement_correspondence_certificate`

## Official Rocq

```coq
supremum_in :
forall {T : eqType} (R : rel (Equality.sort T)) (x : Equality.sort T) (s : seq (Equality.sort T)),
@supremum T R s = @Some (Equality.sort T) x -> is_true (x \in s)

supremum_in is not universe polymorphic
Arguments supremum_in {T} R x s%seq_scope _
supremum_in is opaque
Expands to: Constant prosa.util.supremum.supremum_in
Declared in library prosa.util.supremum, line 67, characters 8-19
@supremum_in
     : forall (T : eqType) (R : rel (Equality.sort T)) (x : Equality.sort T) (s : seq (Equality.sort T)),
       @supremum T R s = @Some (Equality.sort T) x -> is_true (x \in s)
```

## Lean

```lean
@Prosa.Util.Supremum.supremum_in : ∀ {T : Type u_1} [DecidableEq T] (R : T → T → Bool) (x : T) (s : List T),
  Prosa.Util.Supremum.supremum R s = some x → x ∈ s
```

## Lean, imported into Rocq

```coq
Prosa_Util_Supremum_supremum_in
     : forall T : Type,
       DecidableEq T ->
       forall (R : T -> T -> Bool) (x : T) (s : List T),
       @eq (Option T) (Prosa_Util_Supremum_supremum T R s) (Option_some T x) ->
       Membership_mem T (List T) (List_instMembership T) s x
```
