# `search_arg_none`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.search_arg.search_arg_none`
- Lean: `Prosa.Util.SearchArg.search_arg_none`
- Certificate: `search_arg_none_statement_certificate`

## Official Rocq

```coq
search_arg_none :
forall {T : Type} (f : nat -> T) (P : pred T) (R : rel T) (a b : nat),
@search_arg T f P R a b = @None nat <-> (forall x : nat, is_true (a <= x < b) -> is_true (~~ P (f x)))

search_arg_none is not universe polymorphic
Arguments search_arg_none {T}%type_scope f%function_scope P R (a b)%nat_scope
search_arg_none is opaque
Expands to: Constant prosa.util.search_arg.search_arg_none
Declared in library prosa.util.search_arg, line 75, characters 8-23
@search_arg_none
     : forall (T : Type) (f : nat -> T) (P : pred T) (R : rel T) (a b : nat),
       @search_arg T f P R a b = @None nat <-> (forall x : nat, is_true (a <= x < b) -> is_true (~~ P (f x)))
```

## Lean

```lean
@Prosa.Util.SearchArg.search_arg_none : ∀ {T : Type u_1} (f : ℕ → T) (P : T → Bool) (R : T → T → Bool) (a b : ℕ),
  Prosa.Util.SearchArg.search_arg f P R a b = none ↔ ∀ (x : ℕ), a ≤ x ∧ x < b → P (f x) = false
```

## Lean, imported into Rocq

```coq
Prosa_Util_SearchArg_search_arg_none
     : forall (T : Type) (f : Nat -> T) (P : T -> Bool) (R : T -> T -> Bool) (a b : Nat),
       Iff (@eq (Option_inst1 Nat) (Prosa_Util_SearchArg_search_arg T f P R a b) (Option_none_inst1 Nat))
         (forall x : Nat,
          And (LE_le_inst1 Nat instLENat a x) (LT_lt_inst1 Nat instLTNat x b) ->
          @eq Bool (P (f x)) Bool_false)
```
