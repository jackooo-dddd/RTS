# `max0_2cons_eq`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.list.max0_2cons_eq`
- Lean: `Prosa.Util.List.max0_2cons_eq`
- Certificate: `max0_2cons_eq_statement_certificate`

## Official Rocq

```coq
max0_2cons_eq : forall (x : nat) (xs : seq nat), max0 [:: x, x & xs] = max0 (x :: xs)

max0_2cons_eq is not universe polymorphic
Arguments max0_2cons_eq x%nat_scope xs%seq_scope
max0_2cons_eq is opaque
Expands to: Constant prosa.util.list.max0_2cons_eq
Declared in library prosa.util.list, line 132, characters 6-19
max0_2cons_eq
     : forall (x : nat) (xs : seq nat), max0 [:: x, x & xs] = max0 (x :: xs)
```

## Lean

```lean
Prosa.Util.List.max0_2cons_eq : ∀ (x : ℕ) (xs : List ℕ),
  Prosa.Util.List.max0 (x :: x :: xs) = Prosa.Util.List.max0 (x :: xs)
```

## Lean, imported into Rocq

```coq
Prosa_Util_List_max0_2cons_eq
     : forall (x : Nat) (xs : List_inst1 Nat),
       @eq Nat (Prosa_Util_List_max0 (List_cons_inst1 Nat x (List_cons_inst1 Nat x xs)))
         (Prosa_Util_List_max0 (List_cons_inst1 Nat x xs))
```
