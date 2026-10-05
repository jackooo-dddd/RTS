# `max_distance_in_seq_le_last_element_of_seq`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.nondecreasing.max_distance_in_seq_le_last_element_of_seq`
- Lean: `Prosa.Util.Nondecreasing.max_distance_in_seq_le_last_element_of_seq`
- Certificate: `max_distance_in_seq_le_last_element_of_seq_correspondence_certificate`

## Official Rocq

```coq
max_distance_in_seq_le_last_element_of_seq :
forall xs : seq nat, nondecreasing_sequence xs -> is_true (max0 (distances xs) <= last0 xs)

max_distance_in_seq_le_last_element_of_seq is not universe polymorphic
Arguments max_distance_in_seq_le_last_element_of_seq xs%seq_scope _
max_distance_in_seq_le_last_element_of_seq is opaque
Expands to: Constant prosa.util.nondecreasing.max_distance_in_seq_le_last_element_of_seq
Declared in library prosa.util.nondecreasing, line 654, characters 8-50
max_distance_in_seq_le_last_element_of_seq
     : forall xs : seq nat, nondecreasing_sequence xs -> is_true (max0 (distances xs) <= last0 xs)
```

## Lean

```lean
Prosa.Util.Nondecreasing.max_distance_in_seq_le_last_element_of_seq : ∀ (xs : List ℕ),
  Prosa.Util.Nondecreasing.nondecreasing_sequence xs →
    Prosa.Util.List.max0 (Prosa.Util.Nondecreasing.distances xs) ≤ Prosa.Util.List.last0 xs
```

## Lean, imported into Rocq

```coq
Prosa_Util_Nondecreasing_max_distance_in_seq_le_last_element_of_seq
     : forall xs : List_inst1 Nat,
       Prosa_Util_Nondecreasing_nondecreasing_sequence xs ->
       LE_le_inst1 Nat instLENat (Prosa_Util_List_max0 (Prosa_Util_Nondecreasing_distances xs))
         (Prosa_Util_List_last0 xs)
```
