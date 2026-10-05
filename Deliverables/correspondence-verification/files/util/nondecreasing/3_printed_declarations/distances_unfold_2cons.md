# `distances_unfold_2cons`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.nondecreasing.distances_unfold_2cons`
- Lean: `Prosa.Util.Nondecreasing.distances_unfold_2cons`
- Certificate: `distances_unfold_2cons_correspondence_certificate`

## Official Rocq

```coq
distances_unfold_2cons :
forall (x0 x1 : nat) (xs : seq nat), distances [:: x0, x1 & xs] = x1 - x0 :: distances (x1 :: xs)

distances_unfold_2cons is not universe polymorphic
Arguments distances_unfold_2cons (x0 x1)%nat_scope xs%seq_scope
distances_unfold_2cons is opaque
Expands to: Constant prosa.util.nondecreasing.distances_unfold_2cons
Declared in library prosa.util.nondecreasing, line 422, characters 8-30
distances_unfold_2cons
     : forall (x0 x1 : nat) (xs : seq nat), distances [:: x0, x1 & xs] = x1 - x0 :: distances (x1 :: xs)
```

## Lean

```lean
Prosa.Util.Nondecreasing.distances_unfold_2cons : ∀ (x0 x1 : ℕ) (xs : List ℕ),
  Prosa.Util.Nondecreasing.distances (x0 :: x1 :: xs) = (x1 - x0) :: Prosa.Util.Nondecreasing.distances (x1 :: xs)
```

## Lean, imported into Rocq

```coq
Prosa_Util_Nondecreasing_distances_unfold_2cons
     : forall (x0 x1 : Nat) (xs : List_inst1 Nat),
       @eq (List_inst1 Nat)
         (Prosa_Util_Nondecreasing_distances (List_cons_inst1 Nat x0 (List_cons_inst1 Nat x1 xs)))
         (List_cons_inst1 Nat (HSub_hSub_inst7 Nat Nat Nat (instHSub_inst1 Nat instSubNat) x1 x0)
            (Prosa_Util_Nondecreasing_distances (List_cons_inst1 Nat x1 xs)))
```
