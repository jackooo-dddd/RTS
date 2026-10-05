# `in_max0_le`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.list.in_max0_le`
- Lean: `Prosa.Util.List.in_max0_le`
- Certificate: `in_max0_le_statement_certificate`

## Official Rocq

```coq
in_max0_le :
forall (xs : @pred_sort nat (seq_predType Datatypes_nat__canonical__eqtype_Equality)) (x : nat),
is_true (x \in xs) -> is_true (x <= max0 xs)

in_max0_le is not universe polymorphic
Arguments in_max0_le xs x%nat_scope _
in_max0_le is opaque
Expands to: Constant prosa.util.list.in_max0_le
Declared in library prosa.util.list, line 103, characters 6-16
in_max0_le
     : forall (xs : @pred_sort nat (seq_predType Datatypes_nat__canonical__eqtype_Equality)) (x : nat),
       is_true (x \in xs) -> is_true (x <= max0 xs)
```

## Lean

```lean
Prosa.Util.List.in_max0_le : ∀ (xs : List ℕ) (x : ℕ), x ∈ xs → x ≤ Prosa.Util.List.max0 xs
```

## Lean, imported into Rocq

```coq
Prosa_Util_List_in_max0_le
     : forall (xs : List_inst1 Nat) (x : Nat),
       Membership_mem_inst3 Nat (List_inst1 Nat) (List_instMembership_inst1 Nat) xs x ->
       LE_le_inst1 Nat instLENat x (Prosa_Util_List_max0 xs)
```
