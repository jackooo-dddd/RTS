# `search_arg_in_range`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.search_arg.search_arg_in_range`
- Lean: `Prosa.Util.SearchArg.search_arg_in_range`
- Certificate: `search_arg_in_range_statement_certificate`

## Official Rocq

```coq
search_arg_in_range :
forall {T : Type} (f : nat -> T) (P : pred T) (R : rel T) (a b x : nat),
@search_arg T f P R a b = @Some nat x -> is_true (a <= x < b)

search_arg_in_range is not universe polymorphic
Arguments search_arg_in_range {T}%type_scope f%function_scope P R (a b x)%nat_scope _
search_arg_in_range is opaque
Expands to: Constant prosa.util.search_arg.search_arg_in_range
Declared in library prosa.util.search_arg, line 151, characters 8-27
@search_arg_in_range
     : forall (T : Type) (f : nat -> T) (P : pred T) (R : rel T) (a b x : nat),
       @search_arg T f P R a b = @Some nat x -> is_true (a <= x < b)
```

## Lean

```lean
@Prosa.Util.SearchArg.search_arg_in_range : ∀ {T : Type u_1} (f : ℕ → T) (P : T → Bool) (R : T → T → Bool) (a b x : ℕ),
  Prosa.Util.SearchArg.search_arg f P R a b = some x → a ≤ x ∧ x < b
```

## Lean, imported into Rocq

```coq
Prosa_Util_SearchArg_search_arg_in_range
     : forall (T : Type) (f : Nat -> T) (P : T -> Bool) (R : T -> T -> Bool) (a b x : Nat),
       @eq (Option_inst1 Nat) (Prosa_Util_SearchArg_search_arg T f P R a b) (Option_some_inst1 Nat x) ->
       And (LE_le_inst1 Nat instLENat a x) (LT_lt_inst1 Nat instLTNat x b)
```
