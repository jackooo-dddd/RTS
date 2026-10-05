# `belonging_to_segment_of_seq_is_total`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.nondecreasing.belonging_to_segment_of_seq_is_total`
- Lean: `Prosa.Util.Nondecreasing.belonging_to_segment_of_seq_is_total`
- Certificate: `belonging_to_segment_of_seq_is_total_correspondence_certificate`

## Official Rocq

```coq
belonging_to_segment_of_seq_is_total :
forall (xs : seq nat) (x : nat),
is_true (1 < @size nat xs) ->
is_true (first0 xs <= x < last0 xs) ->
exists n : nat, is_true (n.+1 < @size nat xs) /\ is_true (@nth nat 0 xs n <= x < @nth nat 0 xs n.+1)

belonging_to_segment_of_seq_is_total is not universe polymorphic
Arguments belonging_to_segment_of_seq_is_total xs%seq_scope x%nat_scope _ _
belonging_to_segment_of_seq_is_total is opaque
Expands to: Constant prosa.util.nondecreasing.belonging_to_segment_of_seq_is_total
Declared in library prosa.util.nondecreasing, line 243, characters 8-44
belonging_to_segment_of_seq_is_total
     : forall (xs : seq nat) (x : nat),
       is_true (1 < @size nat xs) ->
       is_true (first0 xs <= x < last0 xs) ->
       exists n : nat, is_true (n.+1 < @size nat xs) /\ is_true (@nth nat 0 xs n <= x < @nth nat 0 xs n.+1)
```

## Lean

```lean
Prosa.Util.Nondecreasing.belonging_to_segment_of_seq_is_total : ∀ (xs : List ℕ) (x : ℕ),
  2 ≤ xs.length →
    Prosa.Util.List.first0 xs ≤ x ∧ x < Prosa.Util.List.last0 xs →
      ∃ n, n + 1 < xs.length ∧ Prosa.Util.Nondecreasing.nthD✝ xs n ≤ x ∧ x < Prosa.Util.Nondecreasing.nthD✝ xs (n + 1)
```

## Lean, imported into Rocq

```coq
Prosa_Util_Nondecreasing_belonging_to_segment_of_seq_is_total
     : forall (xs : List_inst1 Nat) (x : Nat),
       LE_le_inst1 Nat instLENat (OfNat_ofNat_inst1 Nat 2 (instOfNatNat 2)) (List_length_inst1 Nat xs) ->
       And (LE_le_inst1 Nat instLENat (Prosa_Util_List_first0 xs) x)
         (LT_lt_inst1 Nat instLTNat x (Prosa_Util_List_last0 xs)) ->
       Exists Nat
         (fun n : Nat =>
          And
            (LT_lt_inst1 Nat instLTNat
               (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat) n
                  (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1)))
               (List_length_inst1 Nat xs))
            (And
               (LE_le_inst1 Nat instLENat
                  (_private_Prosa_Util_Nondecreasing0_Prosa_Util_Nondecreasing_nthD xs n) x)
               (LT_lt_inst1 Nat instLTNat x
                  (_private_Prosa_Util_Nondecreasing0_Prosa_Util_Nondecreasing_nthD xs
                     (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat) n
                        (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1)))))))
```
