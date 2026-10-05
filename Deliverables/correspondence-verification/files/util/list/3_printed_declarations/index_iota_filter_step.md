# `index_iota_filter_step`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.list.index_iota_filter_step`
- Lean: `Prosa.Util.List.index_iota_filter_step`
- Certificate: `index_iota_filter_step_statement_certificate`

## Official Rocq

```coq
index_iota_filter_step :
forall (x : nat) (xs : @pred_sort nat (seq_predType Datatypes_nat__canonical__eqtype_Equality)) (a b : nat),
is_true (a <= x < b) ->
(forall y : nat, is_true (y \in xs) -> is_true (x <= y)) ->
x :: [seq ρ <- bigop.index_iota a b | ρ \in @rem_all Datatypes_nat__canonical__eqtype_Equality x xs]

index_iota_filter_step is not universe polymorphic
Arguments index_iota_filter_step x%nat_scope xs (a b)%nat_scope _ _%function_scope
index_iota_filter_step is opaque
Expands to: Constant prosa.util.list.index_iota_filter_step
Declared in library prosa.util.list, line 754, characters 6-28
index_iota_filter_step
     : forall (x : nat) (xs : @pred_sort nat (seq_predType Datatypes_nat__canonical__eqtype_Equality))
         (a b : nat),
       is_true (a <= x < b) ->
       (forall y : nat, is_true (y \in xs) -> is_true (x <= y)) ->
       [seq ρ <- bigop.index_iota a b | ρ \in x :: xs] =
       x :: [seq ρ <- bigop.index_iota a b | ρ \in @rem_all Datatypes_nat__canonical__eqtype_Equality x xs]
```

## Lean

```lean
Prosa.Util.List.index_iota_filter_step : ∀ (x : ℕ) (xs : List ℕ) (a b : ℕ),
  a ≤ x ∧ x < b →
    (∀ (y : ℕ), y ∈ xs → x ≤ y) →
      List.filter (fun ρ => decide (ρ ∈ x :: xs)) (Prosa.Util.List.index_iota a b) =
        x :: List.filter (fun ρ => decide (ρ ∈ Prosa.Util.List.rem_all x xs)) (Prosa.Util.List.index_iota a b)
```

## Lean, imported into Rocq

```coq
Prosa_Util_List_index_iota_filter_step
     : forall (x : Nat) (xs : List_inst1 Nat) (a b : Nat),
       And (LE_le_inst1 Nat instLENat a x) (LT_lt_inst1 Nat instLTNat x b) ->
       (forall y : Nat,
        Membership_mem_inst3 Nat (List_inst1 Nat) (List_instMembership_inst1 Nat) xs y ->
        LE_le_inst1 Nat instLENat x y) ->
       @eq (List_inst1 Nat)
         (List_filter_inst1 Nat
            (fun _UU03c1_ : Nat =>
             Decidable_decide
               (Membership_mem_inst3 Nat (List_inst1 Nat) (List_instMembership_inst1 Nat)
                  (List_cons_inst1 Nat x xs) _UU03c1_)
               (List_instDecidableMemOfLawfulBEq_inst1 Nat
                  (instBEqOfDecidableEq_inst1 Nat instDecidableEqNat) Nat_instLawfulBEq _UU03c1_
                  (List_cons_inst1 Nat x xs)))
            (Prosa_Util_List_index_iota a b))
         (List_cons_inst1 Nat x
            (List_filter_inst1 Nat
               (fun _UU03c1_ : Nat =>
                Decidable_decide
                  (Membership_mem_inst3 Nat (List_inst1 Nat) (List_instMembership_inst1 Nat)
                     (Prosa_Util_List_rem_all_inst1 Nat instDecidableEqNat x xs) _UU03c1_)
                  (List_instDecidableMemOfLawfulBEq_inst1 Nat
                     (instBEqOfDecidableEq_inst1 Nat instDecidableEqNat) Nat_instLawfulBEq _UU03c1_
                     (Prosa_Util_List_rem_all_inst1 Nat instDecidableEqNat x xs)))
               (Prosa_Util_List_index_iota a b)))
```
