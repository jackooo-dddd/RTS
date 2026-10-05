# `distances_unfold_1app_last`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.nondecreasing.distances_unfold_1app_last`
- Lean: `Prosa.Util.Nondecreasing.distances_unfold_1app_last`
- Certificate: `distances_unfold_1app_last_correspondence_certificate`

## Official Rocq

```coq
distances_unfold_1app_last :
forall (x : nat) (xs : seq nat),
is_true (0 < @size nat xs) -> distances (xs ++ [:: x]) = distances xs ++ [:: x - last0 xs]

distances_unfold_1app_last is not universe polymorphic
Arguments distances_unfold_1app_last x%nat_scope xs%seq_scope _
distances_unfold_1app_last is opaque
Expands to: Constant prosa.util.nondecreasing.distances_unfold_1app_last
Declared in library prosa.util.nondecreasing, line 453, characters 8-34
distances_unfold_1app_last
     : forall (x : nat) (xs : seq nat),
       is_true (0 < @size nat xs) -> distances (xs ++ [:: x]) = distances xs ++ [:: x - last0 xs]
```

## Lean

```lean
Prosa.Util.Nondecreasing.distances_unfold_1app_last : ∀ (x : ℕ) (xs : List ℕ),
  xs.length ≥ 1 →
    Prosa.Util.Nondecreasing.distances (xs ++ [x]) =
      Prosa.Util.Nondecreasing.distances xs ++ [x - Prosa.Util.List.last0 xs]
```

## Lean, imported into Rocq

```coq
Prosa_Util_Nondecreasing_distances_unfold_1app_last
     : forall (x : Nat) (xs : List_inst1 Nat),
       GE_ge_inst1 Nat instLENat (List_length_inst1 Nat xs) (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1)) ->
       @eq (List_inst1 Nat)
         (Prosa_Util_Nondecreasing_distances
            (HAppend_hAppend_inst7 (List_inst1 Nat) (List_inst1 Nat) (List_inst1 Nat)
               (instHAppendOfAppend_inst1 (List_inst1 Nat) (List_instAppend_inst1 Nat)) xs
               (List_cons_inst1 Nat x (List_nil_inst1 Nat))))
         (HAppend_hAppend_inst7 (List_inst1 Nat) (List_inst1 Nat) (List_inst1 Nat)
            (instHAppendOfAppend_inst1 (List_inst1 Nat) (List_instAppend_inst1 Nat))
            (Prosa_Util_Nondecreasing_distances xs)
            (List_cons_inst1 Nat
               (HSub_hSub_inst7 Nat Nat Nat (instHSub_inst1 Nat instSubNat) x (Prosa_Util_List_last0 xs))
               (List_nil_inst1 Nat)))
```
