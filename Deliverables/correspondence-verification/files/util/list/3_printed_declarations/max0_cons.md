# `max0_cons`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.list.max0_cons`
- Lean: `Prosa.Util.List.max0_cons`
- Certificate: `max0_cons_statement_certificate`

## Official Rocq

```coq
max0_cons : forall (x : nat) (xs : seq nat), max0 (x :: xs) = maxn x (max0 xs)

max0_cons is not universe polymorphic
Arguments max0_cons x%nat_scope xs%seq_scope
max0_cons is opaque
Expands to: Constant prosa.util.list.max0_cons
Declared in library prosa.util.list, line 79, characters 6-15
max0_cons
     : forall (x : nat) (xs : seq nat), max0 (x :: xs) = maxn x (max0 xs)
```

## Lean

```lean
Prosa.Util.List.max0_cons : ∀ (x : ℕ) (xs : List ℕ), Prosa.Util.List.max0 (x :: xs) = x.max (Prosa.Util.List.max0 xs)
```

## Lean, imported into Rocq

```coq
Prosa_Util_List_max0_cons
     : forall (x : Nat) (xs : List_inst1 Nat),
       @eq Nat (Prosa_Util_List_max0 (List_cons_inst1 Nat x xs)) (Nat_max x (Prosa_Util_List_max0 xs))
```
