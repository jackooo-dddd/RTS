# `max0_of_uniform_set`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.list.max0_of_uniform_set`
- Lean: `Prosa.Util.List.max0_of_uniform_set`
- Certificate: `max0_of_uniform_set_statement_certificate`

## Official Rocq

```coq
max0_of_uniform_set :
forall (k : Equality.sort Datatypes_nat__canonical__eqtype_Equality)
  (xs : seq (Equality.sort Datatypes_nat__canonical__eqtype_Equality)),
is_true (0 < @size (Equality.sort Datatypes_nat__canonical__eqtype_Equality) xs) ->
(forall x : Equality.sort Datatypes_nat__canonical__eqtype_Equality, is_true (x \in xs) -> x = k) ->
max0 xs = k

max0_of_uniform_set is not universe polymorphic
Arguments max0_of_uniform_set k xs%seq_scope _ _%function_scope
max0_of_uniform_set is opaque
Expands to: Constant prosa.util.list.max0_of_uniform_set
Declared in library prosa.util.list, line 84, characters 6-25
max0_of_uniform_set
     : forall (k : Equality.sort Datatypes_nat__canonical__eqtype_Equality)
         (xs : seq (Equality.sort Datatypes_nat__canonical__eqtype_Equality)),
       is_true (0 < @size (Equality.sort Datatypes_nat__canonical__eqtype_Equality) xs) ->
       (forall x : Equality.sort Datatypes_nat__canonical__eqtype_Equality, is_true (x \in xs) -> x = k) ->
       max0 xs = k
```

## Lean

```lean
Prosa.Util.List.max0_of_uniform_set : ∀ (k : ℕ) (xs : List ℕ),
  xs.length > 0 → (∀ (x : ℕ), x ∈ xs → x = k) → Prosa.Util.List.max0 xs = k
```

## Lean, imported into Rocq

```coq
Prosa_Util_List_max0_of_uniform_set
     : forall (k : Nat) (xs : List_inst1 Nat),
       GT_gt_inst1 Nat instLTNat (List_length_inst1 Nat xs) (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0)) ->
       (forall x : Nat,
        Membership_mem_inst3 Nat (List_inst1 Nat) (List_instMembership_inst1 Nat) xs x -> @eq Nat x k) ->
       @eq Nat (Prosa_Util_List_max0 xs) k
```
