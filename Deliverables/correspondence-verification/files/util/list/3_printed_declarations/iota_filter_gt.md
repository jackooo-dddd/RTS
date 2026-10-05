# `iota_filter_gt`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.list.iota_filter_gt`
- Lean: `Prosa.Util.List.iota_filter_gt`
- Certificate: `iota_filter_gt_statement_certificate`

## Official Rocq

```coq
iota_filter_gt :
forall (x a b idx : nat) (P : nat -> bool),
is_true (x < a) ->
is_true (idx < @size nat [seq x0 <- bigop.index_iota a b | P x0]) ->
is_true (x < @nth nat 0 [seq x0 <- bigop.index_iota a b | P x0] idx)

iota_filter_gt is not universe polymorphic
Arguments iota_filter_gt (x a b idx)%nat_scope P%function_scope _ _
iota_filter_gt is opaque
Expands to: Constant prosa.util.list.iota_filter_gt
Declared in library prosa.util.list, line 813, characters 6-20
iota_filter_gt
     : forall (x a b idx : nat) (P : nat -> bool),
       is_true (x < a) ->
       is_true (idx < @size nat [seq x0 <- bigop.index_iota a b | P x0]) ->
       is_true (x < @nth nat 0 [seq x0 <- bigop.index_iota a b | P x0] idx)
```

## Lean

```lean
Prosa.Util.List.iota_filter_gt : ∀ (x a b idx : ℕ) (P : ℕ → Bool),
  x < a →
    idx < (List.filter P (Prosa.Util.List.index_iota a b)).length →
      x < (List.filter P (Prosa.Util.List.index_iota a b)).getD idx 0
```

## Lean, imported into Rocq

```coq
Prosa_Util_List_iota_filter_gt
     : forall (x a b idx : Nat) (P : Nat -> Bool),
       LT_lt_inst1 Nat instLTNat x a ->
       LT_lt_inst1 Nat instLTNat idx
         (List_length_inst1 Nat (List_filter_inst1 Nat P (Prosa_Util_List_index_iota a b))) ->
       LT_lt_inst1 Nat instLTNat x
         (List_getD_inst1 Nat (List_filter_inst1 Nat P (Prosa_Util_List_index_iota a b)) idx
            (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0)))
```
