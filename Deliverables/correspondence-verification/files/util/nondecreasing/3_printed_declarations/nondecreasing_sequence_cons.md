# `nondecreasing_sequence_cons`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.nondecreasing.nondecreasing_sequence_cons`
- Lean: `Prosa.Util.Nondecreasing.nondecreasing_sequence_cons`
- Certificate: `nondecreasing_sequence_cons_correspondence_certificate`

## Official Rocq

```coq
nondecreasing_sequence_cons :
forall (x : nat) (xs : seq nat), nondecreasing_sequence (x :: xs) -> nondecreasing_sequence xs

nondecreasing_sequence_cons is not universe polymorphic
Arguments nondecreasing_sequence_cons x%nat_scope xs%seq_scope _ n1 n2 _
nondecreasing_sequence_cons is opaque
Expands to: Constant prosa.util.nondecreasing.nondecreasing_sequence_cons
Declared in library prosa.util.nondecreasing, line 122, characters 8-35
nondecreasing_sequence_cons
     : forall (x : nat) (xs : seq nat), nondecreasing_sequence (x :: xs) -> nondecreasing_sequence xs
```

## Lean

```lean
Prosa.Util.Nondecreasing.nondecreasing_sequence_cons : ∀ (x : ℕ) (xs : List ℕ),
  Prosa.Util.Nondecreasing.nondecreasing_sequence (x :: xs) → Prosa.Util.Nondecreasing.nondecreasing_sequence xs
```

## Lean, imported into Rocq

```coq
Prosa_Util_Nondecreasing_nondecreasing_sequence_cons
     : forall (x : Nat) (xs : List_inst1 Nat),
       Prosa_Util_Nondecreasing_nondecreasing_sequence (List_cons_inst1 Nat x xs) ->
       Prosa_Util_Nondecreasing_nondecreasing_sequence xs
```
