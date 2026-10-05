# `nondecreasing_sequence_cons_min`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.nondecreasing.nondecreasing_sequence_cons_min`
- Lean: `Prosa.Util.Nondecreasing.nondecreasing_sequence_cons_min`
- Certificate: `nondecreasing_sequence_cons_min_correspondence_certificate`

## Official Rocq

```coq
nondecreasing_sequence_cons_min :
forall (x : nat) (xs : seq nat),
nondecreasing_sequence (x :: xs) ->
forall y : Equality.sort Datatypes_nat__canonical__eqtype_Equality, is_true (y \in xs) -> is_true (x <= y)

nondecreasing_sequence_cons_min is not universe polymorphic
Arguments nondecreasing_sequence_cons_min x%nat_scope xs%seq_scope _ y _
nondecreasing_sequence_cons_min is opaque
Expands to: Constant prosa.util.nondecreasing.nondecreasing_sequence_cons_min
Declared in library prosa.util.nondecreasing, line 173, characters 8-39
nondecreasing_sequence_cons_min
     : forall (x : nat) (xs : seq nat),
       nondecreasing_sequence (x :: xs) ->
       forall y : Equality.sort Datatypes_nat__canonical__eqtype_Equality,
       is_true (y \in xs) -> is_true (x <= y)
```

## Lean

```lean
Prosa.Util.Nondecreasing.nondecreasing_sequence_cons_min : ∀ (x : ℕ) (xs : List ℕ),
  Prosa.Util.Nondecreasing.nondecreasing_sequence (x :: xs) → ∀ y ∈ xs, x ≤ y
```

## Lean, imported into Rocq

```coq
Prosa_Util_Nondecreasing_nondecreasing_sequence_cons_min
     : forall (x : Nat) (xs : List_inst1 Nat),
       Prosa_Util_Nondecreasing_nondecreasing_sequence (List_cons_inst1 Nat x xs) ->
       forall y : Nat,
       Membership_mem_inst3 Nat (List_inst1 Nat) (List_instMembership_inst1 Nat) xs y ->
       LE_le_inst1 Nat instLENat x y
```
