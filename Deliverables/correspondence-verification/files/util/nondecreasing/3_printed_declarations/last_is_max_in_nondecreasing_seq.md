# `last_is_max_in_nondecreasing_seq`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.nondecreasing.last_is_max_in_nondecreasing_seq`
- Lean: `Prosa.Util.Nondecreasing.last_is_max_in_nondecreasing_seq`
- Certificate: `last_is_max_in_nondecreasing_seq_correspondence_certificate`

## Official Rocq

```coq
last_is_max_in_nondecreasing_seq :
forall (xs : seq nat) (x : nat), nondecreasing_sequence xs -> is_true (x \in xs) -> is_true (x <= last0 xs)

last_is_max_in_nondecreasing_seq is not universe polymorphic
Arguments last_is_max_in_nondecreasing_seq xs%seq_scope x%nat_scope _ _
last_is_max_in_nondecreasing_seq is opaque
Expands to: Constant prosa.util.nondecreasing.last_is_max_in_nondecreasing_seq
Declared in library prosa.util.nondecreasing, line 281, characters 8-40
last_is_max_in_nondecreasing_seq
     : forall (xs : seq nat) (x : nat),
       nondecreasing_sequence xs -> is_true (x \in xs) -> is_true (x <= last0 xs)
```

## Lean

```lean
Prosa.Util.Nondecreasing.last_is_max_in_nondecreasing_seq : ∀ (xs : List ℕ) (x : ℕ),
  Prosa.Util.Nondecreasing.nondecreasing_sequence xs → x ∈ xs → x ≤ Prosa.Util.List.last0 xs
```

## Lean, imported into Rocq

```coq
Prosa_Util_Nondecreasing_last_is_max_in_nondecreasing_seq
     : forall (xs : List_inst1 Nat) (x : Nat),
       Prosa_Util_Nondecreasing_nondecreasing_sequence xs ->
       Membership_mem_inst3 Nat (List_inst1 Nat) (List_instMembership_inst1 Nat) xs x ->
       LE_le_inst1 Nat instLENat x (Prosa_Util_List_last0 xs)
```
