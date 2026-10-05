# `rem_lt_id`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.list.rem_lt_id`
- Lean: `Prosa.Util.List.rem_lt_id`
- Certificate: `rem_lt_id_statement_certificate`

## Official Rocq

```coq
rem_lt_id :
forall (x : nat) (xs : @pred_sort nat (seq_predType Datatypes_nat__canonical__eqtype_Equality)),
(forall y : nat, is_true (y \in xs) -> is_true (x < y)) ->
@rem_all Datatypes_nat__canonical__eqtype_Equality x xs = xs

rem_lt_id is not universe polymorphic
Arguments rem_lt_id x%nat_scope xs _%function_scope
rem_lt_id is opaque
Expands to: Constant prosa.util.list.rem_lt_id
Declared in library prosa.util.list, line 613, characters 6-15
rem_lt_id
     : forall (x : nat) (xs : @pred_sort nat (seq_predType Datatypes_nat__canonical__eqtype_Equality)),
       (forall y : nat, is_true (y \in xs) -> is_true (x < y)) ->
       @rem_all Datatypes_nat__canonical__eqtype_Equality x xs = xs
```

## Lean

```lean
Prosa.Util.List.rem_lt_id : ∀ (x : ℕ) (xs : List ℕ), (∀ (y : ℕ), y ∈ xs → x < y) → Prosa.Util.List.rem_all x xs = xs
```

## Lean, imported into Rocq

```coq
Prosa_Util_List_rem_lt_id
     : forall (x : Nat) (xs : List_inst1 Nat),
       (forall y : Nat,
        Membership_mem_inst3 Nat (List_inst1 Nat) (List_instMembership_inst1 Nat) xs y ->
        LT_lt_inst1 Nat instLTNat x y) ->
       @eq (List_inst1 Nat) (Prosa_Util_List_rem_all_inst1 Nat instDecidableEqNat x xs) xs
```
