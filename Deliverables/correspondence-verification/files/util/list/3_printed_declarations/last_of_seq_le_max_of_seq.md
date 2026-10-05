# `last_of_seq_le_max_of_seq`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.list.last_of_seq_le_max_of_seq`
- Lean: `Prosa.Util.List.last_of_seq_le_max_of_seq`
- Certificate: `last_of_seq_le_max_of_seq_statement_certificate`

## Official Rocq

```coq
last_of_seq_le_max_of_seq : forall xs : seq nat, is_true (last0 xs <= max0 xs)

last_of_seq_le_max_of_seq is not universe polymorphic
Arguments last_of_seq_le_max_of_seq xs%seq_scope
last_of_seq_le_max_of_seq is opaque
Expands to: Constant prosa.util.list.last_of_seq_le_max_of_seq
Declared in library prosa.util.list, line 161, characters 6-31
last_of_seq_le_max_of_seq
     : forall xs : seq nat, is_true (last0 xs <= max0 xs)
```

## Lean

```lean
Prosa.Util.List.last_of_seq_le_max_of_seq : ∀ (xs : List ℕ), Prosa.Util.List.last0 xs ≤ Prosa.Util.List.max0 xs
```

## Lean, imported into Rocq

```coq
Prosa_Util_List_last_of_seq_le_max_of_seq
     : forall xs : List_inst1 Nat,
       LE_le_inst1 Nat instLENat (Prosa_Util_List_last0 xs) (Prosa_Util_List_max0 xs)
```
