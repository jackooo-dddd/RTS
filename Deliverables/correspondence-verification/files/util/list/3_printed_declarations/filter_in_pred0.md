# `filter_in_pred0`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.list.filter_in_pred0`
- Lean: `Prosa.Util.List.filter_in_pred0`
- Certificate: `filter_in_pred0_statement_certificate`

## Official Rocq

```coq
filter_in_pred0 :
forall {X : eqType} (xs : seq (Equality.sort X)) (P : pred (Equality.sort X)),
(forall x : Equality.sort X, is_true (x \in xs) -> is_true (~~ P x)) -> [seq x <- xs | P x] = [::]

filter_in_pred0 is not universe polymorphic
Arguments filter_in_pred0 {X} xs%seq_scope P _%function_scope
filter_in_pred0 is opaque
Expands to: Constant prosa.util.list.filter_in_pred0
Declared in library prosa.util.list, line 421, characters 6-21
@filter_in_pred0
     : forall (X : eqType) (xs : seq (Equality.sort X)) (P : pred (Equality.sort X)),
       (forall x : Equality.sort X, is_true (x \in xs) -> is_true (~~ P x)) -> [seq x <- xs | P x] = [::]
```

## Lean

```lean
@Prosa.Util.List.filter_in_pred0 : ∀ {T : Type u_1} [DecidableEq T] (xs : List T) (P : T → Bool),
  (∀ (x : T), x ∈ xs → P x = false) → List.filter P xs = []
```

## Lean, imported into Rocq

```coq
Prosa_Util_List_filter_in_pred0
     : forall T : Type,
       DecidableEq T ->
       forall (xs : List T) (P : T -> Bool),
       (forall x : T, Membership_mem T (List T) (List_instMembership T) xs x -> @eq Bool (P x) Bool_false) ->
       @eq (List T) (List_filter T P xs) (List_nil T)
```
