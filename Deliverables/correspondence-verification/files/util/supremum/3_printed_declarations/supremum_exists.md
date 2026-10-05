# `supremum_exists`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.supremum.supremum_exists`
- Lean: `Prosa.Util.Supremum.supremum_exists`
- Certificate: `supremum_exists_statement_correspondence_certificate`

## Official Rocq

```coq
supremum_exists :
forall {T : eqType} (R : rel (Equality.sort T)) (x : Equality.sort T)
  (s : @pred_sort (Equality.sort T) (seq_predType T)),
is_true (x \in s) -> is_true (@supremum T R s != @None (Equality.sort T))

supremum_exists is not universe polymorphic
Arguments supremum_exists {T} R x s _
supremum_exists is opaque
Expands to: Constant prosa.util.supremum.supremum_exists
Declared in library prosa.util.supremum, line 45, characters 8-23
@supremum_exists
     : forall (T : eqType) (R : rel (Equality.sort T)) (x : Equality.sort T)
         (s : @pred_sort (Equality.sort T) (seq_predType T)),
       is_true (x \in s) -> is_true (@supremum T R s != @None (Equality.sort T))
```

## Lean

```lean
@Prosa.Util.Supremum.supremum_exists : ∀ {T : Type u_1} [DecidableEq T] (R : T → T → Bool) (x : T) (s : List T),
  x ∈ s → Prosa.Util.Supremum.supremum R s ≠ none
```

## Lean, imported into Rocq

```coq
Prosa_Util_Supremum_supremum_exists
     : forall T : Type,
       DecidableEq T ->
       forall (R : T -> T -> Bool) (x : T) (s : List T),
       Membership_mem T (List T) (List_instMembership T) s x ->
       Ne (Option T) (Prosa_Util_Supremum_supremum T R s) (Option_none T)
```
