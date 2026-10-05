# `range_iota_filter_step`

- Kind (Rocq): Corollary
- Rocq: `prosa.util.list.range_iota_filter_step`
- Lean: `Prosa.Util.List.range_iota_filter_step`
- Certificate: `range_iota_filter_step_statement_certificate`

## Official Rocq

```coq
range_iota_filter_step :
forall (x : nat) (xs : @pred_sort nat (seq_predType Datatypes_nat__canonical__eqtype_Equality)) (k : nat),
is_true (x <= k) ->
(forall y : nat, is_true (y \in xs) -> is_true (x <= y)) ->
x :: [seq ρ <- range 0 k | ρ \in @rem_all Datatypes_nat__canonical__eqtype_Equality x xs]

range_iota_filter_step is not universe polymorphic
Arguments range_iota_filter_step x%nat_scope xs k%nat_scope _ _%function_scope
range_iota_filter_step is opaque
Expands to: Constant prosa.util.list.range_iota_filter_step
Declared in library prosa.util.list, line 800, characters 10-32
range_iota_filter_step
     : forall (x : nat) (xs : @pred_sort nat (seq_predType Datatypes_nat__canonical__eqtype_Equality))
         (k : nat),
       is_true (x <= k) ->
       (forall y : nat, is_true (y \in xs) -> is_true (x <= y)) ->
       [seq ρ <- range 0 k | ρ \in x :: xs] =
       x :: [seq ρ <- range 0 k | ρ \in @rem_all Datatypes_nat__canonical__eqtype_Equality x xs]
```

## Lean

```lean
Prosa.Util.List.range_iota_filter_step : ∀ (x : ℕ) (xs : List ℕ) (k : ℕ),
  x ≤ k →
    (∀ (y : ℕ), y ∈ xs → x ≤ y) →
      List.filter (fun ρ => decide (ρ ∈ x :: xs)) (Prosa.Util.List.range 0 k) =
        x :: List.filter (fun ρ => decide (ρ ∈ Prosa.Util.List.rem_all x xs)) (Prosa.Util.List.range 0 k)
```

## Lean, imported into Rocq

```coq
Prosa_Util_List_range_iota_filter_step
     : forall (x : Nat) (xs : List_inst1 Nat) (k : Nat),
       LE_le_inst1 Nat instLENat x k ->
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
            (Prosa_Util_List_range (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0)) k))
         (List_cons_inst1 Nat x
            (List_filter_inst1 Nat
               (fun _UU03c1_ : Nat =>
                Decidable_decide
                  (Membership_mem_inst3 Nat (List_inst1 Nat) (List_instMembership_inst1 Nat)
                     (Prosa_Util_List_rem_all_inst1 Nat instDecidableEqNat x xs) _UU03c1_)
                  (List_instDecidableMemOfLawfulBEq_inst1 Nat
                     (instBEqOfDecidableEq_inst1 Nat instDecidableEqNat) Nat_instLawfulBEq _UU03c1_
                     (Prosa_Util_List_rem_all_inst1 Nat instDecidableEqNat x xs)))
               (Prosa_Util_List_range (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0)) k)))
```
