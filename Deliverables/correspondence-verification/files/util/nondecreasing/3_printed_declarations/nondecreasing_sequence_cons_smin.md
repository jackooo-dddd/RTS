# `nondecreasing_sequence_cons_smin`

- Kind (Rocq): Corollary
- Rocq: `prosa.util.nondecreasing.nondecreasing_sequence_cons_smin`
- Lean: `Prosa.Util.Nondecreasing.nondecreasing_sequence_cons_smin`
- Certificate: `nondecreasing_sequence_cons_smin_correspondence_certificate`

## Official Rocq

```coq
nondecreasing_sequence_cons_smin :
forall (x1 x2 : nat) (xs : seq nat),
is_true (x1 < x2) ->
nondecreasing_sequence [:: x1, x2 & xs] ->
forall y : Equality.sort Datatypes_nat__canonical__eqtype_Equality,
is_true (y \in x2 :: xs) -> is_true (x1 < y)

nondecreasing_sequence_cons_smin is not universe polymorphic
Arguments nondecreasing_sequence_cons_smin (x1 x2)%nat_scope xs%seq_scope _ _ y _
nondecreasing_sequence_cons_smin is opaque
Expands to: Constant prosa.util.nondecreasing.nondecreasing_sequence_cons_smin
Declared in library prosa.util.nondecreasing, line 189, characters 12-44
nondecreasing_sequence_cons_smin
     : forall (x1 x2 : nat) (xs : seq nat),
       is_true (x1 < x2) ->
       nondecreasing_sequence [:: x1, x2 & xs] ->
       forall y : Equality.sort Datatypes_nat__canonical__eqtype_Equality,
       is_true (y \in x2 :: xs) -> is_true (x1 < y)
```

## Lean

```lean
Prosa.Util.Nondecreasing.nondecreasing_sequence_cons_smin : ∀ (x1 x2 : ℕ) (xs : List ℕ),
  x1 < x2 → Prosa.Util.Nondecreasing.nondecreasing_sequence (x1 :: x2 :: xs) → ∀ y ∈ x2 :: xs, x1 < y
```

## Lean, imported into Rocq

```coq
Prosa_Util_Nondecreasing_nondecreasing_sequence_cons_smin
     : forall (x1 x2 : Nat) (xs : List_inst1 Nat),
       LT_lt_inst1 Nat instLTNat x1 x2 ->
       Prosa_Util_Nondecreasing_nondecreasing_sequence (List_cons_inst1 Nat x1 (List_cons_inst1 Nat x2 xs)) ->
       forall y : Nat,
       Membership_mem_inst3 Nat (List_inst1 Nat) (List_instMembership_inst1 Nat) 
         (List_cons_inst1 Nat x2 xs) y ->
       LT_lt_inst1 Nat instLTNat x1 y
```
