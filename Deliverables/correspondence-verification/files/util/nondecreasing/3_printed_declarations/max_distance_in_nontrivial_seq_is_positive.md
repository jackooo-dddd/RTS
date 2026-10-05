# `max_distance_in_nontrivial_seq_is_positive`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.nondecreasing.max_distance_in_nontrivial_seq_is_positive`
- Lean: `Prosa.Util.Nondecreasing.max_distance_in_nontrivial_seq_is_positive`
- Certificate: `max_distance_in_nontrivial_seq_is_positive_correspondence_certificate`

## Official Rocq

```coq
max_distance_in_nontrivial_seq_is_positive :
forall xs : seq nat,
nondecreasing_sequence xs ->
(exists x y : Equality.sort Datatypes_nat__canonical__eqtype_Equality,
   is_true (x \in xs) /\ is_true (y \in xs) /\ x <> y) ->
is_true (0 < max0 (distances xs))

max_distance_in_nontrivial_seq_is_positive is not universe polymorphic
Arguments max_distance_in_nontrivial_seq_is_positive xs%seq_scope _ _
max_distance_in_nontrivial_seq_is_positive is opaque
Expands to: Constant prosa.util.nondecreasing.max_distance_in_nontrivial_seq_is_positive
Declared in library prosa.util.nondecreasing, line 584, characters 8-50
max_distance_in_nontrivial_seq_is_positive
     : forall xs : seq nat,
       nondecreasing_sequence xs ->
       (exists x y : Equality.sort Datatypes_nat__canonical__eqtype_Equality,
          is_true (x \in xs) /\ is_true (y \in xs) /\ x <> y) ->
       is_true (0 < max0 (distances xs))
```

## Lean

```lean
Prosa.Util.Nondecreasing.max_distance_in_nontrivial_seq_is_positive : ∀ (xs : List ℕ),
  Prosa.Util.Nondecreasing.nondecreasing_sequence xs →
    (∃ x y, x ∈ xs ∧ y ∈ xs ∧ x ≠ y) → 0 < Prosa.Util.List.max0 (Prosa.Util.Nondecreasing.distances xs)
```

## Lean, imported into Rocq

```coq
Prosa_Util_Nondecreasing_max_distance_in_nontrivial_seq_is_positive
     : forall xs : List_inst1 Nat,
       Prosa_Util_Nondecreasing_nondecreasing_sequence xs ->
       Exists Nat
         (fun x : Nat =>
          Exists Nat
            (fun y : Nat =>
             And (Membership_mem_inst3 Nat (List_inst1 Nat) (List_instMembership_inst1 Nat) xs x)
               (And (Membership_mem_inst3 Nat (List_inst1 Nat) (List_instMembership_inst1 Nat) xs y)
                  (Ne Nat x y)))) ->
       LT_lt_inst1 Nat instLTNat (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0))
         (Prosa_Util_List_max0 (Prosa_Util_Nondecreasing_distances xs))
```
