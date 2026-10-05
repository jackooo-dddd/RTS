# `last0_cons`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.list.last0_cons`
- Lean: `Prosa.Util.List.last0_cons`
- Certificate: `last0_cons_statement_certificate`

## Official Rocq

```coq
last0_cons : forall (x : nat) (xs : seq nat), xs <> [::] -> last0 (x :: xs) = last0 xs

last0_cons is not universe polymorphic
Arguments last0_cons x%nat_scope xs%seq_scope _
last0_cons is opaque
Expands to: Constant prosa.util.list.last0_cons
Declared in library prosa.util.list, line 19, characters 6-16
last0_cons
     : forall (x : nat) (xs : seq nat), xs <> [::] -> last0 (x :: xs) = last0 xs
```

## Lean

```lean
Prosa.Util.List.last0_cons : ∀ (x : ℕ) (xs : List ℕ),
  xs ≠ [] → Prosa.Util.List.last0 (x :: xs) = Prosa.Util.List.last0 xs
```

## Lean, imported into Rocq

```coq
Prosa_Util_List_last0_cons
     : forall (x : Nat) (xs : List_inst1 Nat),
       Ne (List_inst1 Nat) xs (List_nil_inst1 Nat) ->
       @eq Nat (Prosa_Util_List_last0 (List_cons_inst1 Nat x xs)) (Prosa_Util_List_last0 xs)
```
