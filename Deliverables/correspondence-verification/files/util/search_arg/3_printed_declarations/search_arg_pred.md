# `search_arg_pred`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.search_arg.search_arg_pred`
- Lean: `Prosa.Util.SearchArg.search_arg_pred`
- Certificate: `search_arg_pred_statement_certificate`

## Official Rocq

```coq
search_arg_pred :
forall {T : Type} (f : nat -> T) (P : pred T) (R : rel T) (a b x : nat),
@search_arg T f P R a b = @Some nat x -> is_true (P (f x))

search_arg_pred is not universe polymorphic
Arguments search_arg_pred {T}%type_scope f%function_scope P R (a b x)%nat_scope _
search_arg_pred is opaque
Expands to: Constant prosa.util.search_arg.search_arg_pred
Declared in library prosa.util.search_arg, line 134, characters 8-23
@search_arg_pred
     : forall (T : Type) (f : nat -> T) (P : pred T) (R : rel T) (a b x : nat),
       @search_arg T f P R a b = @Some nat x -> is_true (P (f x))
```

## Lean

```lean
@Prosa.Util.SearchArg.search_arg_pred : ∀ {T : Type u_1} (f : ℕ → T) (P : T → Bool) (R : T → T → Bool) (a b x : ℕ),
  Prosa.Util.SearchArg.search_arg f P R a b = some x → P (f x) = true
```

## Lean, imported into Rocq

```coq
Prosa_Util_SearchArg_search_arg_pred
     : forall (T : Type) (f : Nat -> T) (P : T -> Bool) (R : T -> T -> Bool) (a b x : Nat),
       @eq (Option_inst1 Nat) (Prosa_Util_SearchArg_search_arg T f P R a b) (Option_some_inst1 Nat x) ->
       @eq Bool (P (f x)) Bool_true
```
