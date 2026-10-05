# `supremum_unfold`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.supremum.supremum_unfold`
- Lean: `Prosa.Util.Supremum.supremum_unfold`
- Certificate: `supremum_unfold_statement_correspondence_certificate`

## Official Rocq

```coq
supremum_unfold :
forall {T : eqType} (R : rel (Equality.sort T)) (head : Equality.sort T) (tail : seq (Equality.sort T)),
@supremum T R (head :: tail) = @choose_superior T R head (@supremum T R tail)

supremum_unfold is not universe polymorphic
Arguments supremum_unfold {T} R head tail%seq_scope
supremum_unfold is opaque
Expands to: Constant prosa.util.supremum.supremum_unfold
Declared in library prosa.util.supremum, line 35, characters 8-23
@supremum_unfold
     : forall (T : eqType) (R : rel (Equality.sort T)) (head : Equality.sort T)
         (tail : seq (Equality.sort T)),
       @supremum T R (head :: tail) = @choose_superior T R head (@supremum T R tail)
```

## Lean

```lean
@Prosa.Util.Supremum.supremum_unfold : ∀ {T : Type u_1} [DecidableEq T] (R : T → T → Bool) (head : T) (tail : List T),
  Prosa.Util.Supremum.supremum R (head :: tail) =
    Prosa.Util.Supremum.choose_superior R head (Prosa.Util.Supremum.supremum R tail)
```

## Lean, imported into Rocq

```coq
Prosa_Util_Supremum_supremum_unfold
     : forall T : Type,
       DecidableEq T ->
       forall (R : T -> T -> Bool) (head : T) (tail : List T),
       @eq (Option T) (Prosa_Util_Supremum_supremum T R (List_cons T head tail))
         (Prosa_Util_Supremum_choose_superior T R head (Prosa_Util_Supremum_supremum T R tail))
```
