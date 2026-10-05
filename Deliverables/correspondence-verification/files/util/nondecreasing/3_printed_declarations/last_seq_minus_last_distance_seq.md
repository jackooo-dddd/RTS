# `last_seq_minus_last_distance_seq`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.nondecreasing.last_seq_minus_last_distance_seq`
- Lean: `Prosa.Util.Nondecreasing.last_seq_minus_last_distance_seq`
- Certificate: `last_seq_minus_last_distance_seq_correspondence_certificate`

## Official Rocq

```coq
last_seq_minus_last_distance_seq :
forall xs : seq nat,
nondecreasing_sequence xs -> last0 xs - last0 (distances xs) = @nth nat 0 xs (@size nat xs).-2

last_seq_minus_last_distance_seq is not universe polymorphic
Arguments last_seq_minus_last_distance_seq xs%seq_scope _
last_seq_minus_last_distance_seq is opaque
Expands to: Constant prosa.util.nondecreasing.last_seq_minus_last_distance_seq
Declared in library prosa.util.nondecreasing, line 634, characters 8-40
last_seq_minus_last_distance_seq
     : forall xs : seq nat,
       nondecreasing_sequence xs -> last0 xs - last0 (distances xs) = @nth nat 0 xs (@size nat xs).-2
```

## Lean

```lean
Prosa.Util.Nondecreasing.last_seq_minus_last_distance_seq : ∀ (xs : List ℕ),
  Prosa.Util.Nondecreasing.nondecreasing_sequence xs →
    Prosa.Util.List.last0 xs - Prosa.Util.List.last0 (Prosa.Util.Nondecreasing.distances xs) =
      Prosa.Util.Nondecreasing.nthD✝ xs (xs.length - 2)
```

## Lean, imported into Rocq

```coq
Prosa_Util_Nondecreasing_last_seq_minus_last_distance_seq
     : forall xs : List_inst1 Nat,
       Prosa_Util_Nondecreasing_nondecreasing_sequence xs ->
       @eq Nat
         (HSub_hSub_inst7 Nat Nat Nat (instHSub_inst1 Nat instSubNat) (Prosa_Util_List_last0 xs)
            (Prosa_Util_List_last0 (Prosa_Util_Nondecreasing_distances xs)))
         (_private_Prosa_Util_Nondecreasing0_Prosa_Util_Nondecreasing_nthD xs
            (HSub_hSub_inst7 Nat Nat Nat (instHSub_inst1 Nat instSubNat) (List_length_inst1 Nat xs)
               (OfNat_ofNat_inst1 Nat 2 (instOfNatNat 2))))
```
