# `max0_2cons_le`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.list.max0_2cons_le`
- Lean: `Prosa.Util.List.max0_2cons_le`
- Certificate: `max0_2cons_le_statement_certificate`

## Official Rocq

```coq
max0_2cons_le :
forall (x1 x2 : nat) (xs : seq nat), is_true (x1 <= x2) -> max0 [:: x1, x2 & xs] = max0 (x2 :: xs)

max0_2cons_le is not universe polymorphic
Arguments max0_2cons_le (x1 x2)%nat_scope xs%seq_scope _
max0_2cons_le is opaque
Expands to: Constant prosa.util.list.max0_2cons_le
Declared in library prosa.util.list, line 140, characters 6-19
max0_2cons_le
     : forall (x1 x2 : nat) (xs : seq nat), is_true (x1 <= x2) -> max0 [:: x1, x2 & xs] = max0 (x2 :: xs)
```

## Lean

```lean
Prosa.Util.List.max0_2cons_le : ∀ (x1 x2 : ℕ) (xs : List ℕ),
  x1 ≤ x2 → Prosa.Util.List.max0 (x1 :: x2 :: xs) = Prosa.Util.List.max0 (x2 :: xs)
```

## Lean, imported into Rocq

```coq
Prosa_Util_List_max0_2cons_le
     : forall (x1 x2 : Nat) (xs : List_inst1 Nat),
       LE_le_inst1 Nat instLENat x1 x2 ->
       @eq Nat (Prosa_Util_List_max0 (List_cons_inst1 Nat x1 (List_cons_inst1 Nat x2 xs)))
         (Prosa_Util_List_max0 (List_cons_inst1 Nat x2 xs))
```
