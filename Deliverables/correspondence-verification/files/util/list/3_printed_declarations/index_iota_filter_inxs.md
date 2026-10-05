# `index_iota_filter_inxs`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.list.index_iota_filter_inxs`
- Lean: `Prosa.Util.List.index_iota_filter_inxs`
- Certificate: `index_iota_filter_inxs_statement_certificate`

## Official Rocq

```coq
index_iota_filter_inxs :
forall (a b x : nat) (xs : @pred_sort nat (seq_predType Datatypes_nat__canonical__eqtype_Equality)),
is_true (x < a) ->

index_iota_filter_inxs is not universe polymorphic
Arguments index_iota_filter_inxs (a b x)%nat_scope xs _
index_iota_filter_inxs is opaque
Expands to: Constant prosa.util.list.index_iota_filter_inxs
Declared in library prosa.util.list, line 733, characters 6-28
index_iota_filter_inxs
     : forall (a b x : nat) (xs : @pred_sort nat (seq_predType Datatypes_nat__canonical__eqtype_Equality)),
       is_true (x < a) ->
       [seq ρ <- bigop.index_iota a b | ρ \in xs] =
       [seq ρ <- bigop.index_iota a b | ρ \in @rem_all Datatypes_nat__canonical__eqtype_Equality x xs]
```

## Lean

```lean
Prosa.Util.List.index_iota_filter_inxs : ∀ (a b x : ℕ) (xs : List ℕ),
  x < a →
    List.filter (fun ρ => decide (ρ ∈ xs)) (Prosa.Util.List.index_iota a b) =
      List.filter (fun ρ => decide (ρ ∈ Prosa.Util.List.rem_all x xs)) (Prosa.Util.List.index_iota a b)
```

## Lean, imported into Rocq

```coq
Prosa_Util_List_index_iota_filter_inxs
     : forall (a b x : Nat) (xs : List_inst1 Nat),
       LT_lt_inst1 Nat instLTNat x a ->
       @eq (List_inst1 Nat)
         (List_filter_inst1 Nat
            (fun _UU03c1_ : Nat =>
             Decidable_decide
               (Membership_mem_inst3 Nat (List_inst1 Nat) (List_instMembership_inst1 Nat) xs _UU03c1_)
               (List_instDecidableMemOfLawfulBEq_inst1 Nat
                  (instBEqOfDecidableEq_inst1 Nat instDecidableEqNat) Nat_instLawfulBEq _UU03c1_ xs))
            (Prosa_Util_List_index_iota a b))
         (List_filter_inst1 Nat
            (fun _UU03c1_ : Nat =>
             Decidable_decide
               (Membership_mem_inst3 Nat (List_inst1 Nat) (List_instMembership_inst1 Nat)
                  (Prosa_Util_List_rem_all_inst1 Nat instDecidableEqNat x xs) _UU03c1_)
               (List_instDecidableMemOfLawfulBEq_inst1 Nat
                  (instBEqOfDecidableEq_inst1 Nat instDecidableEqNat) Nat_instLawfulBEq _UU03c1_
                  (Prosa_Util_List_rem_all_inst1 Nat instDecidableEqNat x xs)))
            (Prosa_Util_List_index_iota a b))
```
