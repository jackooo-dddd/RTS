# `max0_in_seq`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.list.max0_in_seq`
- Lean: `Prosa.Util.List.max0_in_seq`
- Certificate: `max0_in_seq_statement_certificate`

## Official Rocq

```coq
max0_in_seq : forall xs : seq nat, xs <> [::] -> is_true (max0 xs \in xs)

max0_in_seq is not universe polymorphic
Arguments max0_in_seq xs%seq_scope _
max0_in_seq is opaque
Expands to: Constant prosa.util.list.max0_in_seq
Declared in library prosa.util.list, line 114, characters 6-17
max0_in_seq
     : forall xs : seq nat, xs <> [::] -> is_true (max0 xs \in xs)
```

## Lean

```lean
Prosa.Util.List.max0_in_seq : ∀ (xs : List ℕ), xs ≠ [] → Prosa.Util.List.max0 xs ∈ xs
```

## Lean, imported into Rocq

```coq
Prosa_Util_List_max0_in_seq
     : forall xs : List_inst1 Nat,
       Ne (List_inst1 Nat) xs (List_nil_inst1 Nat) ->
       Membership_mem_inst3 Nat (List_inst1 Nat) (List_instMembership_inst1 Nat) xs (Prosa_Util_List_max0 xs)
```
