# `distance_between_neighboring_elements_le_max_distance_in_seq`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.nondecreasing.distance_between_neighboring_elements_le_max_distance_in_seq`
- Lean: `Prosa.Util.Nondecreasing.distance_between_neighboring_elements_le_max_distance_in_seq`
- Certificate: `distance_between_neighboring_elements_le_max_distance_in_seq_correspondence_certificate`

## Official Rocq

```coq
distance_between_neighboring_elements_le_max_distance_in_seq :
forall (xs : seq nat) (n : nat), is_true (@nth nat 0 xs n.+1 - @nth nat 0 xs n <= max0 (distances xs))

distance_between_neighboring_elements_le_max_distance_in_seq is not universe polymorphic
Arguments distance_between_neighboring_elements_le_max_distance_in_seq xs%seq_scope n%nat_scope
distance_between_neighboring_elements_le_max_distance_in_seq is opaque
Expands to: Constant prosa.util.nondecreasing.distance_between_neighboring_elements_le_max_distance_in_seq
Declared in library prosa.util.nondecreasing, line 475, characters 8-68
distance_between_neighboring_elements_le_max_distance_in_seq
     : forall (xs : seq nat) (n : nat), is_true (@nth nat 0 xs n.+1 - @nth nat 0 xs n <= max0 (distances xs))
```

## Lean

```lean
Prosa.Util.Nondecreasing.distance_between_neighboring_elements_le_max_distance_in_seq : ∀ (xs : List ℕ) (n : ℕ),
  Prosa.Util.Nondecreasing.nthD✝ xs (n + 1) - Prosa.Util.Nondecreasing.nthD✝ xs n ≤
    Prosa.Util.List.max0 (Prosa.Util.Nondecreasing.distances xs)
```

## Lean, imported into Rocq

```coq
Prosa_Util_Nondecreasing_distance_between_neighboring_elements_le_max_distance_in_seq
     : forall (xs : List_inst1 Nat) (n : Nat),
       LE_le_inst1 Nat instLENat
         (HSub_hSub_inst7 Nat Nat Nat (instHSub_inst1 Nat instSubNat)
            (_private_Prosa_Util_Nondecreasing0_Prosa_Util_Nondecreasing_nthD xs
               (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat) n
                  (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1))))
            (_private_Prosa_Util_Nondecreasing0_Prosa_Util_Nondecreasing_nthD xs n))
         (Prosa_Util_List_max0 (Prosa_Util_Nondecreasing_distances xs))
```
