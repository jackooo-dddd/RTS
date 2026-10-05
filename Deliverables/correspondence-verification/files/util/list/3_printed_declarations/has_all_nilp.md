# `has_all_nilp`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.list.has_all_nilp`
- Lean: `Prosa.Util.List.has_all_nilp`
- Certificate: `has_all_nilp_statement_certificate`

## Official Rocq

```coq
has_all_nilp :
forall {T : eqType} (s : seq (Equality.sort T)) (P : pred (Equality.sort T)),
is_true (@all (Equality.sort T) P s) ->
is_true (~~ @nilp (Equality.sort T) s) -> is_true (@has (Equality.sort T) P s)

has_all_nilp is not universe polymorphic
Arguments has_all_nilp {T} s%seq_scope P _ _
has_all_nilp is opaque
Expands to: Constant prosa.util.list.has_all_nilp
Declared in library prosa.util.list, line 483, characters 6-18
@has_all_nilp
     : forall (T : eqType) (s : seq (Equality.sort T)) (P : pred (Equality.sort T)),
       is_true (@all (Equality.sort T) P s) ->
       is_true (~~ @nilp (Equality.sort T) s) -> is_true (@has (Equality.sort T) P s)
```

## Lean

```lean
@Prosa.Util.List.has_all_nilp : ∀ {T : Type u_1} [DecidableEq T] (s : List T) (P : T → Bool),
  s.all P = true → s.isEmpty = false → s.any P = true
```

## Lean, imported into Rocq

```coq
Prosa_Util_List_has_all_nilp
     : forall T : Type,
       DecidableEq T ->
       forall (s : List T) (P : T -> Bool),
       @eq Bool (List_all T s P) Bool_true ->
       @eq Bool (List_isEmpty T s) Bool_false -> @eq Bool (List_any T s P) Bool_true
```
