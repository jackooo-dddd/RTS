# `search_arg_not_none`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.search_arg.search_arg_not_none`
- Lean: `Prosa.Util.SearchArg.search_arg_not_none`
- Certificate: `search_arg_not_none_statement_certificate`

## Official Rocq

```coq
search_arg_not_none :
forall {T : Type} (f : nat -> T) (P : pred T) (R : rel T) (a b : nat),
(exists x : nat, is_true (a <= x < b) /\ is_true (P (f x))) ->
exists y : nat, @search_arg T f P R a b = @Some nat y

search_arg_not_none is not universe polymorphic
Arguments search_arg_not_none {T}%type_scope f%function_scope P R (a b)%nat_scope _
search_arg_not_none is opaque
Expands to: Constant prosa.util.search_arg.search_arg_not_none
Declared in library prosa.util.search_arg, line 119, characters 8-27
@search_arg_not_none
     : forall (T : Type) (f : nat -> T) (P : pred T) (R : rel T) (a b : nat),
       (exists x : nat, is_true (a <= x < b) /\ is_true (P (f x))) ->
       exists y : nat, @search_arg T f P R a b = @Some nat y
```

## Lean

```lean
@Prosa.Util.SearchArg.search_arg_not_none : ∀ {T : Type u_1} (f : ℕ → T) (P : T → Bool) (R : T → T → Bool) (a b : ℕ),
  (∃ x, (a ≤ x ∧ x < b) ∧ P (f x) = true) → ∃ y, Prosa.Util.SearchArg.search_arg f P R a b = some y
```

## Lean, imported into Rocq

```coq
Prosa_Util_SearchArg_search_arg_not_none
     : forall (T : Type) (f : Nat -> T) (P : T -> Bool) (R : T -> T -> Bool) (a b : Nat),
       Exists Nat
         (fun x : Nat =>
          And (And (LE_le_inst1 Nat instLENat a x) (LT_lt_inst1 Nat instLTNat x b))
            (@eq Bool (P (f x)) Bool_true)) ->
       Exists Nat (fun y : Nat => Prosa_Util_SearchArg_search_arg T f P R a b = Option_some_inst1 Nat y)
```
