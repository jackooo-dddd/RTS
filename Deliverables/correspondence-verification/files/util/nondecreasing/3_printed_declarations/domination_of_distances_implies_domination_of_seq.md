# `domination_of_distances_implies_domination_of_seq`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.nondecreasing.domination_of_distances_implies_domination_of_seq`
- Lean: `Prosa.Util.Nondecreasing.domination_of_distances_implies_domination_of_seq`
- Certificate: `domination_of_distances_implies_domination_of_seq_correspondence_certificate`

## Official Rocq

```coq
domination_of_distances_implies_domination_of_seq :
forall xs ys : seq nat,
is_true (first0 xs <= first0 ys) ->
is_true (1 < @size nat xs) ->
is_true (1 < @size nat ys) ->
@size nat xs = @size nat ys ->
nondecreasing_sequence xs ->
nondecreasing_sequence ys ->
(forall n : nat, is_true (@nth nat 0 (distances xs) n <= @nth nat 0 (distances ys) n)) ->
forall n : nat, is_true (@nth nat 0 xs n <= @nth nat 0 ys n)

domination_of_distances_implies_domination_of_seq is not universe polymorphic
Arguments domination_of_distances_implies_domination_of_seq (xs ys)%seq_scope _ _ 
  _ _ _ _ _%function_scope n%nat_scope
domination_of_distances_implies_domination_of_seq is opaque
Expands to: Constant prosa.util.nondecreasing.domination_of_distances_implies_domination_of_seq
Declared in library prosa.util.nondecreasing, line 775, characters 8-57
domination_of_distances_implies_domination_of_seq
     : forall xs ys : seq nat,
       is_true (first0 xs <= first0 ys) ->
       is_true (1 < @size nat xs) ->
       is_true (1 < @size nat ys) ->
       @size nat xs = @size nat ys ->
       nondecreasing_sequence xs ->
       nondecreasing_sequence ys ->
       (forall n : nat, is_true (@nth nat 0 (distances xs) n <= @nth nat 0 (distances ys) n)) ->
       forall n : nat, is_true (@nth nat 0 xs n <= @nth nat 0 ys n)
```

## Lean

```lean
Prosa.Util.Nondecreasing.domination_of_distances_implies_domination_of_seq : ∀ (xs ys : List ℕ),
  Prosa.Util.List.first0 xs ≤ Prosa.Util.List.first0 ys →
    2 ≤ xs.length →
      2 ≤ ys.length →
        xs.length = ys.length →
          Prosa.Util.Nondecreasing.nondecreasing_sequence xs →
            Prosa.Util.Nondecreasing.nondecreasing_sequence ys →
              (∀ (n : ℕ),
                  Prosa.Util.Nondecreasing.nthD✝ (Prosa.Util.Nondecreasing.distances xs) n ≤
                    Prosa.Util.Nondecreasing.nthD✝ (Prosa.Util.Nondecreasing.distances ys) n) →
                ∀ (n : ℕ), Prosa.Util.Nondecreasing.nthD✝ xs n ≤ Prosa.Util.Nondecreasing.nthD✝ ys n
```

## Lean, imported into Rocq

```coq
Prosa_Util_Nondecreasing_domination_of_distances_implies_domination_of_seq
     : forall xs ys : List_inst1 Nat,
       LE_le_inst1 Nat instLENat (Prosa_Util_List_first0 xs) (Prosa_Util_List_first0 ys) ->
       LE_le_inst1 Nat instLENat (OfNat_ofNat_inst1 Nat 2 (instOfNatNat 2)) (List_length_inst1 Nat xs) ->
       LE_le_inst1 Nat instLENat (OfNat_ofNat_inst1 Nat 2 (instOfNatNat 2)) (List_length_inst1 Nat ys) ->
       @eq Nat (List_length_inst1 Nat xs) (List_length_inst1 Nat ys) ->
       Prosa_Util_Nondecreasing_nondecreasing_sequence xs ->
       Prosa_Util_Nondecreasing_nondecreasing_sequence ys ->
       (forall n : Nat,
        LE_le_inst1 Nat instLENat
          (_private_Prosa_Util_Nondecreasing0_Prosa_Util_Nondecreasing_nthD
             (Prosa_Util_Nondecreasing_distances xs) n)
          (_private_Prosa_Util_Nondecreasing0_Prosa_Util_Nondecreasing_nthD
             (Prosa_Util_Nondecreasing_distances ys) n)) ->
       forall n : Nat,
       LE_le_inst1 Nat instLENat (_private_Prosa_Util_Nondecreasing0_Prosa_Util_Nondecreasing_nthD xs n)
         (_private_Prosa_Util_Nondecreasing0_Prosa_Util_Nondecreasing_nthD ys n)
```
