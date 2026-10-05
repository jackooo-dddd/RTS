# `distances_iota_filtered`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.nondecreasing.distances_iota_filtered`
- Lean: `Prosa.Util.Nondecreasing.distances_iota_filtered`
- Certificate: `distances_iota_filtered_correspondence_certificate`

## Official Rocq

```coq
distances_iota_filtered :
forall (xs : @pred_sort nat (seq_predType Datatypes_nat__canonical__eqtype_Equality)) (k : nat),
(forall x : nat, is_true (x \in xs) -> is_true (x <= k)) ->
nondecreasing_sequence xs ->
distances [seq ρ <- bigop.index_iota 0 k.+1 | ρ \in xs] = [seq x <- distances xs | 0 < x]

distances_iota_filtered is not universe polymorphic
Arguments distances_iota_filtered xs k%nat_scope _%function_scope _
distances_iota_filtered is opaque
Expands to: Constant prosa.util.nondecreasing.distances_iota_filtered
Declared in library prosa.util.nondecreasing, line 698, characters 8-31
distances_iota_filtered
     : forall (xs : @pred_sort nat (seq_predType Datatypes_nat__canonical__eqtype_Equality)) (k : nat),
       (forall x : nat, is_true (x \in xs) -> is_true (x <= k)) ->
       nondecreasing_sequence xs ->
       distances [seq ρ <- bigop.index_iota 0 k.+1 | ρ \in xs] = [seq x <- distances xs | 0 < x]
```

## Lean

```lean
Prosa.Util.Nondecreasing.distances_iota_filtered : ∀ (xs : List ℕ) (k : ℕ),
  (∀ x ∈ xs, x ≤ k) →
    Prosa.Util.Nondecreasing.nondecreasing_sequence xs →
      Prosa.Util.Nondecreasing.distances
          (List.filter (fun x => decide (x ∈ xs)) (Prosa.Util.List.index_iota 0 (k + 1))) =
        List.filter (fun x => decide (x > 0)) (Prosa.Util.Nondecreasing.distances xs)
```

## Lean, imported into Rocq

```coq
Prosa_Util_Nondecreasing_distances_iota_filtered
     : forall (xs : List_inst1 Nat) (k : Nat),
       (forall x : Nat,
        Membership_mem_inst3 Nat (List_inst1 Nat) (List_instMembership_inst1 Nat) xs x ->
        LE_le_inst1 Nat instLENat x k) ->
       Prosa_Util_Nondecreasing_nondecreasing_sequence xs ->
       @eq (List_inst1 Nat)
         (Prosa_Util_Nondecreasing_distances
            (List_filter_inst1 Nat
               (fun x____at___Prosa_Util_Nondecreasing2635657019__hygCtx__hyg45 : Nat =>
                Decidable_decide
                  (Membership_mem_inst3 Nat (List_inst1 Nat) (List_instMembership_inst1 Nat) xs
                     x____at___Prosa_Util_Nondecreasing2635657019__hygCtx__hyg45)
                  (List_instDecidableMemOfLawfulBEq_inst1 Nat
                     (instBEqOfDecidableEq_inst1 Nat instDecidableEqNat) Nat_instLawfulBEq
                     x____at___Prosa_Util_Nondecreasing2635657019__hygCtx__hyg45 xs))
               (Prosa_Util_List_index_iota (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0))
                  (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat) k
                     (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1))))))
         (List_filter_inst1 Nat
            (fun x____at___Prosa_Util_Nondecreasing2635657019__hygCtx__hyg61 : Nat =>
             Decidable_decide
               (GT_gt_inst1 Nat instLTNat x____at___Prosa_Util_Nondecreasing2635657019__hygCtx__hyg61
                  (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0)))
               (Nat_decLt (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0))
                  x____at___Prosa_Util_Nondecreasing2635657019__hygCtx__hyg61))
            (Prosa_Util_Nondecreasing_distances xs))
```
