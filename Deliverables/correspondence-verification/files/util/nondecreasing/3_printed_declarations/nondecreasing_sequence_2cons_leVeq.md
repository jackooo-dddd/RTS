# `nondecreasing_sequence_2cons_leVeq`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.nondecreasing.nondecreasing_sequence_2cons_leVeq`
- Lean: `Prosa.Util.Nondecreasing.nondecreasing_sequence_2cons_leVeq`
- Certificate: `nondecreasing_sequence_2cons_leVeq_correspondence_certificate`

## Official Rocq

```coq
nondecreasing_sequence_2cons_leVeq :
forall (x1 x2 : nat) (xs : seq nat), nondecreasing_sequence [:: x1, x2 & xs] -> x1 = x2 \/ is_true (x1 < x2)

nondecreasing_sequence_2cons_leVeq is not universe polymorphic
Arguments nondecreasing_sequence_2cons_leVeq (x1 x2)%nat_scope xs%seq_scope _
nondecreasing_sequence_2cons_leVeq is opaque
Expands to: Constant prosa.util.nondecreasing.nondecreasing_sequence_2cons_leVeq
Declared in library prosa.util.nondecreasing, line 109, characters 8-42
nondecreasing_sequence_2cons_leVeq
     : forall (x1 x2 : nat) (xs : seq nat),
       nondecreasing_sequence [:: x1, x2 & xs] -> x1 = x2 \/ is_true (x1 < x2)
```

## Lean

```lean
Prosa.Util.Nondecreasing.nondecreasing_sequence_2cons_leVeq : ∀ (x1 x2 : ℕ) (xs : List ℕ),
  Prosa.Util.Nondecreasing.nondecreasing_sequence (x1 :: x2 :: xs) → x1 = x2 ∨ x1 < x2
```

## Lean, imported into Rocq

```coq
Prosa_Util_Nondecreasing_nondecreasing_sequence_2cons_leVeq
     : forall (x1 x2 : Nat) (xs : List_inst1 Nat),
       Prosa_Util_Nondecreasing_nondecreasing_sequence (List_cons_inst1 Nat x1 (List_cons_inst1 Nat x2 xs)) ->
       Or (@eq Nat x1 x2) (LT_lt_inst1 Nat instLTNat x1 x2)
```
