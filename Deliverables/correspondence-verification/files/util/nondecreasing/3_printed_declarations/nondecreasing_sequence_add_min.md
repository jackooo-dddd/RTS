# `nondecreasing_sequence_add_min`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.nondecreasing.nondecreasing_sequence_add_min`
- Lean: `Prosa.Util.Nondecreasing.nondecreasing_sequence_add_min`
- Certificate: `nondecreasing_sequence_add_min_correspondence_certificate`

## Official Rocq

```coq
nondecreasing_sequence_add_min :
forall (x : nat) (xs : @pred_sort nat (seq_predType Datatypes_nat__canonical__eqtype_Equality)),
(forall y : nat, is_true (y \in xs) -> is_true (x <= y)) ->
nondecreasing_sequence xs -> nondecreasing_sequence (x :: xs)

nondecreasing_sequence_add_min is not universe polymorphic
Arguments nondecreasing_sequence_add_min x%nat_scope xs _%function_scope _ n1 n2 _
nondecreasing_sequence_add_min is opaque
Expands to: Constant prosa.util.nondecreasing.nondecreasing_sequence_add_min
Declared in library prosa.util.nondecreasing, line 139, characters 8-38
nondecreasing_sequence_add_min
     : forall (x : nat) (xs : @pred_sort nat (seq_predType Datatypes_nat__canonical__eqtype_Equality)),
       (forall y : nat, is_true (y \in xs) -> is_true (x <= y)) ->
       nondecreasing_sequence xs -> nondecreasing_sequence (x :: xs)
```

## Lean

```lean
Prosa.Util.Nondecreasing.nondecreasing_sequence_add_min : ∀ (x : ℕ) (xs : List ℕ),
  (∀ y ∈ xs, x ≤ y) →
    Prosa.Util.Nondecreasing.nondecreasing_sequence xs → Prosa.Util.Nondecreasing.nondecreasing_sequence (x :: xs)
```

## Lean, imported into Rocq

```coq
Prosa_Util_Nondecreasing_nondecreasing_sequence_add_min
     : forall (x : Nat) (xs : List_inst1 Nat),
       (forall y : Nat,
        Membership_mem_inst3 Nat (List_inst1 Nat) (List_instMembership_inst1 Nat) xs y ->
        LE_le_inst1 Nat instLENat x y) ->
       Prosa_Util_Nondecreasing_nondecreasing_sequence xs ->
       Prosa_Util_Nondecreasing_nondecreasing_sequence (List_cons_inst1 Nat x xs)
```
