# `supremum_none`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.supremum.supremum_none`
- Lean: `Prosa.Util.Supremum.supremum_none`
- Certificate: `supremum_none_statement_correspondence_certificate`

## Official Rocq

```coq
supremum_none :
forall {T : eqType} (R : rel (Equality.sort T)) (s : seq (Equality.sort T)),
@supremum T R s = @None (Equality.sort T) -> s = [::]

supremum_none is not universe polymorphic
Arguments supremum_none {T} R s%seq_scope _
supremum_none is opaque
Expands to: Constant prosa.util.supremum.supremum_none
Declared in library prosa.util.supremum, line 56, characters 8-21
@supremum_none
     : forall (T : eqType) (R : rel (Equality.sort T)) (s : seq (Equality.sort T)),
       @supremum T R s = @None (Equality.sort T) -> s = [::]
```

## Lean

```lean
@Prosa.Util.Supremum.supremum_none : ∀ {T : Type u_1} [DecidableEq T] (R : T → T → Bool) (s : List T),
  Prosa.Util.Supremum.supremum R s = none → s = []
```

## Lean, imported into Rocq

```coq
Prosa_Util_Supremum_supremum_none
     : forall T : Type,
       DecidableEq T ->
       forall (R : T -> T -> Bool) (s : List T),
       @eq (Option T) (Prosa_Util_Supremum_supremum T R s) (Option_none T) -> @eq (List T) s (List_nil T)
```
