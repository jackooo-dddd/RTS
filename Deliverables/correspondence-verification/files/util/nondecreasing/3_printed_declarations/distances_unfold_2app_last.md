# `distances_unfold_2app_last`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.nondecreasing.distances_unfold_2app_last`
- Lean: `Prosa.Util.Nondecreasing.distances_unfold_2app_last`
- Certificate: `distances_unfold_2app_last_correspondence_certificate`

## Official Rocq

```coq
distances_unfold_2app_last :
forall (a b : nat) (xs : seq nat), distances (xs ++ [:: a; b]) = distances (xs ++ [:: a]) ++ [:: b - a]

distances_unfold_2app_last is not universe polymorphic
Arguments distances_unfold_2app_last (a b)%nat_scope xs%seq_scope
distances_unfold_2app_last is opaque
Expands to: Constant prosa.util.nondecreasing.distances_unfold_2app_last
Declared in library prosa.util.nondecreasing, line 431, characters 8-34
distances_unfold_2app_last
     : forall (a b : nat) (xs : seq nat),
       distances (xs ++ [:: a; b]) = distances (xs ++ [:: a]) ++ [:: b - a]
```

## Lean

```lean
Prosa.Util.Nondecreasing.distances_unfold_2app_last : ∀ (a b : ℕ) (xs : List ℕ),
  Prosa.Util.Nondecreasing.distances (xs ++ [a, b]) = Prosa.Util.Nondecreasing.distances (xs ++ [a]) ++ [b - a]
```

## Lean, imported into Rocq

```coq
Prosa_Util_Nondecreasing_distances_unfold_2app_last
     : forall (a b : Nat) (xs : List_inst1 Nat),
       @eq (List_inst1 Nat)
         (Prosa_Util_Nondecreasing_distances
            (HAppend_hAppend_inst7 (List_inst1 Nat) (List_inst1 Nat) (List_inst1 Nat)
               (instHAppendOfAppend_inst1 (List_inst1 Nat) (List_instAppend_inst1 Nat)) xs
               (List_cons_inst1 Nat a (List_cons_inst1 Nat b (List_nil_inst1 Nat)))))
         (HAppend_hAppend_inst7 (List_inst1 Nat) (List_inst1 Nat) (List_inst1 Nat)
            (instHAppendOfAppend_inst1 (List_inst1 Nat) (List_instAppend_inst1 Nat))
            (Prosa_Util_Nondecreasing_distances
               (HAppend_hAppend_inst7 (List_inst1 Nat) (List_inst1 Nat) (List_inst1 Nat)
                  (instHAppendOfAppend_inst1 (List_inst1 Nat) (List_instAppend_inst1 Nat)) xs
                  (List_cons_inst1 Nat a (List_nil_inst1 Nat))))
            (List_cons_inst1 Nat (HSub_hSub_inst7 Nat Nat Nat (instHSub_inst1 Nat instSubNat) b a)
               (List_nil_inst1 Nat)))
```
