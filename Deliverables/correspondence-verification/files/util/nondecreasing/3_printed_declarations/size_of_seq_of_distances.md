# `size_of_seq_of_distances`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.nondecreasing.size_of_seq_of_distances`
- Lean: `Prosa.Util.Nondecreasing.size_of_seq_of_distances`
- Certificate: `size_of_seq_of_distances_correspondence_certificate`

## Official Rocq

```coq
size_of_seq_of_distances :
forall xs : seq nat, is_true (1 < @size nat xs) -> @size nat xs = @size nat (distances xs) + 1

size_of_seq_of_distances is not universe polymorphic
Arguments size_of_seq_of_distances xs%seq_scope _
size_of_seq_of_distances is opaque
Expands to: Constant prosa.util.nondecreasing.size_of_seq_of_distances
Declared in library prosa.util.nondecreasing, line 539, characters 8-32
size_of_seq_of_distances
     : forall xs : seq nat, is_true (1 < @size nat xs) -> @size nat xs = @size nat (distances xs) + 1
```

## Lean

```lean
Prosa.Util.Nondecreasing.size_of_seq_of_distances : ∀ (xs : List ℕ),
  2 ≤ xs.length → xs.length = (Prosa.Util.Nondecreasing.distances xs).length + 1
```

## Lean, imported into Rocq

```coq
Prosa_Util_Nondecreasing_size_of_seq_of_distances
     : forall xs : List_inst1 Nat,
       LE_le_inst1 Nat instLENat (OfNat_ofNat_inst1 Nat 2 (instOfNatNat 2)) (List_length_inst1 Nat xs) ->
       @eq Nat (List_length_inst1 Nat xs)
         (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat)
            (List_length_inst1 Nat (Prosa_Util_Nondecreasing_distances xs))
            (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1)))
```
