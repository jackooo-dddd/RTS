# `distances_of_iota_ε`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.nondecreasing.distances_of_iota_ε`
- Lean: `Prosa.Util.Nondecreasing.distances_of_iota_ε`
- Certificate: `distances_of_iota_epsilon_correspondence_certificate`

## Official Rocq

```coq
distances_of_iota_ε :
forall (n : nat) (x : Equality.sort Datatypes_nat__canonical__eqtype_Equality),
is_true (x \in distances (bigop.index_iota 0 n)) -> x = 1

distances_of_iota_ε is not universe polymorphic
Arguments distances_of_iota_ε n%nat_scope x _
distances_of_iota_ε is opaque
Expands to: Constant prosa.util.nondecreasing.distances_of_iota_ε
Declared in library prosa.util.nondecreasing, line 564, characters 8-28
distances_of_iota_ε
     : forall (n : nat) (x : Equality.sort Datatypes_nat__canonical__eqtype_Equality),
       is_true (x \in distances (bigop.index_iota 0 n)) -> x = 1
```

## Lean

```lean
Prosa.Util.Nondecreasing.distances_of_iota_ε : ∀ (n x : ℕ),
  x ∈ Prosa.Util.Nondecreasing.distances (Prosa.Util.List.index_iota 0 n) → x = 1
```

## Lean, imported into Rocq

```coq
Prosa_Util_Nondecreasing_distances_of_iota__UU03b5_
     : forall n x : Nat,
       Membership_mem_inst3 Nat (List_inst1 Nat) (List_instMembership_inst1 Nat)
         (Prosa_Util_Nondecreasing_distances
            (Prosa_Util_List_index_iota (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0)) n))
         x ->
       @eq Nat x (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1))
```
