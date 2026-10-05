# `search_arg_extremum`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.search_arg.search_arg_extremum`
- Lean: `Prosa.Util.SearchArg.search_arg_extremum`
- Certificate: `search_arg_extremum_statement_certificate`

## Official Rocq

```coq
search_arg_extremum :
forall {T : Type} (f : nat -> T) (P : pred T) (R : rel T),
@reflexive T R ->
@transitive T R ->
@total T R ->
forall a b x : nat,
@search_arg T f P R a b = @Some nat x ->
forall y : nat, is_true (a <= y < b) -> is_true (P (f y)) -> is_true (R (f x) (f y))

search_arg_extremum is not universe polymorphic
Arguments search_arg_extremum {T}%type_scope f%function_scope P R R_reflexive R_transitive 
  R_total (a b x)%nat_scope _ y%nat_scope _ _
search_arg_extremum is opaque
Expands to: Constant prosa.util.search_arg.search_arg_extremum
Declared in library prosa.util.search_arg, line 181, characters 8-27
@search_arg_extremum
     : forall (T : Type) (f : nat -> T) (P : pred T) (R : rel T),
       @reflexive T R ->
       @transitive T R ->
       @total T R ->
       forall a b x : nat,
       @search_arg T f P R a b = @Some nat x ->
       forall y : nat, is_true (a <= y < b) -> is_true (P (f y)) -> is_true (R (f x) (f y))
```

## Lean

```lean
@Prosa.Util.SearchArg.search_arg_extremum : ∀ {T : Type u_1} (f : ℕ → T) (P : T → Bool) (R : T → T → Bool),
  (∀ (x : T), R x x = true) →
    (∀ (x y z : T), R x y = true → R y z = true → R x z = true) →
      (∀ (x y : T), R x y = true ∨ R y x = true) →
        ∀ (a b x : ℕ),
          Prosa.Util.SearchArg.search_arg f P R a b = some x →
            ∀ (y : ℕ), a ≤ y ∧ y < b → P (f y) = true → R (f x) (f y) = true
```

## Lean, imported into Rocq

```coq
Prosa_Util_SearchArg_search_arg_extremum
     : forall (T : Type) (f : Nat -> T) (P : T -> Bool) (R : T -> T -> Bool),
       (forall x : T, @eq Bool (R x x) Bool_true) ->
       (forall x y z : T,
        @eq Bool (R x y) Bool_true -> @eq Bool (R y z) Bool_true -> @eq Bool (R x z) Bool_true) ->
       (forall x y : T, Or (@eq Bool (R x y) Bool_true) (@eq Bool (R y x) Bool_true)) ->
       forall a b x : Nat,
       @eq (Option_inst1 Nat) (Prosa_Util_SearchArg_search_arg T f P R a b) (Option_some_inst1 Nat x) ->
       forall y : Nat,
       And (LE_le_inst1 Nat instLENat a y) (LT_lt_inst1 Nat instLTNat y b) ->
       @eq Bool (P (f y)) Bool_true -> @eq Bool (R (f x) (f y)) Bool_true
```
