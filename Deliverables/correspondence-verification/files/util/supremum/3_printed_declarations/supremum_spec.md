# `supremum_spec`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.supremum.supremum_spec`
- Lean: `Prosa.Util.Supremum.supremum_spec`
- Certificate: `supremum_spec_statement_correspondence_certificate`

## Official Rocq

```coq
supremum_spec :
forall {T : eqType} (R : rel (Equality.sort T)),
@reflexive (Equality.sort T) R ->
@total (Equality.sort T) R ->
@transitive (Equality.sort T) R ->
forall (x : Equality.sort T) (s : seq (Equality.sort T)),
@supremum T R s = @Some (Equality.sort T) x ->
forall y : Equality.sort T, is_true (y \in s) -> is_true (R x y)

supremum_spec is not universe polymorphic
Arguments supremum_spec {T} R H_R_reflexive H_R_total H_R_transitive x s%seq_scope _ y _
supremum_spec is opaque
Expands to: Constant prosa.util.supremum.supremum_spec
Declared in library prosa.util.supremum, line 97, characters 8-21
@supremum_spec
     : forall (T : eqType) (R : rel (Equality.sort T)),
       @reflexive (Equality.sort T) R ->
       @total (Equality.sort T) R ->
       @transitive (Equality.sort T) R ->
       forall (x : Equality.sort T) (s : seq (Equality.sort T)),
       @supremum T R s = @Some (Equality.sort T) x ->
       forall y : Equality.sort T, is_true (y \in s) -> is_true (R x y)
```

## Lean

```lean
@Prosa.Util.Supremum.supremum_spec : ∀ {T : Type u_1} [DecidableEq T] (R : T → T → Bool),
  (∀ (x : T), R x x = true) →
    (∀ (x y : T), (R x y || R y x) = true) →
      (∀ (x y z : T), R x y = true → R y z = true → R x z = true) →
        ∀ (x : T) (s : List T), Prosa.Util.Supremum.supremum R s = some x → ∀ (y : T), y ∈ s → R x y = true
```

## Lean, imported into Rocq

```coq
Prosa_Util_Supremum_supremum_spec
     : forall T : Type,
       DecidableEq T ->
       forall R : T -> T -> Bool,
       (forall x : T, @eq Bool (R x x) Bool_true) ->
       (forall x y : T, @eq Bool (Bool_or (R x y) (R y x)) Bool_true) ->
       (forall x y z : T,
        @eq Bool (R x y) Bool_true -> @eq Bool (R y z) Bool_true -> @eq Bool (R x z) Bool_true) ->
       forall (x : T) (s : List T),
       @eq (Option T) (Prosa_Util_Supremum_supremum T R s) (Option_some T x) ->
       forall y : T, Membership_mem T (List T) (List_instMembership T) s y -> @eq Bool (R x y) Bool_true
```
