# `nodup_sort_2cons_lt`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.nondecreasing.nodup_sort_2cons_lt`
- Lean: `Prosa.Util.Nondecreasing.nodup_sort_2cons_lt`
- Certificate: `nodup_sort_2cons_lt_correspondence_certificate`

## Official Rocq

```coq
nodup_sort_2cons_lt :
forall (x1 x2 : nat) (xs : seq nat),
is_true (x1 < x2) ->
nondecreasing_sequence [:: x1, x2 & xs] ->
@undup Datatypes_nat__canonical__eqtype_Equality [:: x1, x2 & xs] =
x1 :: @undup Datatypes_nat__canonical__eqtype_Equality (x2 :: xs)

nodup_sort_2cons_lt is not universe polymorphic
Arguments nodup_sort_2cons_lt (x1 x2)%nat_scope xs%seq_scope _ _
nodup_sort_2cons_lt is opaque
Expands to: Constant prosa.util.nondecreasing.nodup_sort_2cons_lt
Declared in library prosa.util.nondecreasing, line 325, characters 8-27
nodup_sort_2cons_lt
     : forall (x1 x2 : nat) (xs : seq nat),
       is_true (x1 < x2) ->
       nondecreasing_sequence [:: x1, x2 & xs] ->
       @undup Datatypes_nat__canonical__eqtype_Equality [:: x1, x2 & xs] =
       x1 :: @undup Datatypes_nat__canonical__eqtype_Equality (x2 :: xs)
```

## Lean

```lean
Prosa.Util.Nondecreasing.nodup_sort_2cons_lt : ∀ (x1 x2 : ℕ) (xs : List ℕ),
  x1 < x2 →
    Prosa.Util.Nondecreasing.nondecreasing_sequence (x1 :: x2 :: xs) → (x1 :: x2 :: xs).dedup = x1 :: (x2 :: xs).dedup
```

## Lean, imported into Rocq

```coq
Prosa_Util_Nondecreasing_nodup_sort_2cons_lt
     : forall (x1 x2 : Nat) (xs : List_inst1 Nat),
       LT_lt_inst1 Nat instLTNat x1 x2 ->
       Prosa_Util_Nondecreasing_nondecreasing_sequence (List_cons_inst1 Nat x1 (List_cons_inst1 Nat x2 xs)) ->
       @eq (List_inst1 Nat)
         (List_dedup_inst1 Nat instDecidableEqNat (List_cons_inst1 Nat x1 (List_cons_inst1 Nat x2 xs)))
         (List_cons_inst1 Nat x1 (List_dedup_inst1 Nat instDecidableEqNat (List_cons_inst1 Nat x2 xs)))
```
