# `nondecreasing_sequence_cons_double`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.nondecreasing.nondecreasing_sequence_cons_double`
- Lean: `Prosa.Util.Nondecreasing.nondecreasing_sequence_cons_double`
- Certificate: `nondecreasing_sequence_cons_double_correspondence_certificate`

## Official Rocq

```coq
nondecreasing_sequence_cons_double :
forall (x : nat) (xs : seq nat), nondecreasing_sequence (x :: xs) -> nondecreasing_sequence [:: x, x & xs]

nondecreasing_sequence_cons_double is not universe polymorphic
Arguments nondecreasing_sequence_cons_double x%nat_scope xs%seq_scope _ n1 n2 _
nondecreasing_sequence_cons_double is opaque
Expands to: Constant prosa.util.nondecreasing.nondecreasing_sequence_cons_double
Declared in library prosa.util.nondecreasing, line 156, characters 8-42
nondecreasing_sequence_cons_double
     : forall (x : nat) (xs : seq nat),
       nondecreasing_sequence (x :: xs) -> nondecreasing_sequence [:: x, x & xs]
```

## Lean

```lean
Prosa.Util.Nondecreasing.nondecreasing_sequence_cons_double : ∀ (x : ℕ) (xs : List ℕ),
  Prosa.Util.Nondecreasing.nondecreasing_sequence (x :: xs) →
    Prosa.Util.Nondecreasing.nondecreasing_sequence (x :: x :: xs)
```

## Lean, imported into Rocq

```coq
Prosa_Util_Nondecreasing_nondecreasing_sequence_cons_double
     : forall (x : Nat) (xs : List_inst1 Nat),
       Prosa_Util_Nondecreasing_nondecreasing_sequence (List_cons_inst1 Nat x xs) ->
       Prosa_Util_Nondecreasing_nondecreasing_sequence (List_cons_inst1 Nat x (List_cons_inst1 Nat x xs))
```
