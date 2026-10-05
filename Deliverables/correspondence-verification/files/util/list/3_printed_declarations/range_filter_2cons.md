# `range_filter_2cons`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.list.range_filter_2cons`
- Lean: `Prosa.Util.List.range_filter_2cons`
- Certificate: `range_filter_2cons_statement_certificate`

## Official Rocq

```coq
range_filter_2cons :
forall (x : Equality.sort Datatypes_nat__canonical__eqtype_Equality)
  (xs : seq (Equality.sort Datatypes_nat__canonical__eqtype_Equality)) (k : nat),

range_filter_2cons is not universe polymorphic
Arguments range_filter_2cons x xs%seq_scope k%nat_scope
range_filter_2cons is opaque
Expands to: Constant prosa.util.list.range_filter_2cons
Declared in library prosa.util.list, line 674, characters 6-24
range_filter_2cons
     : forall (x : Equality.sort Datatypes_nat__canonical__eqtype_Equality)
         (xs : seq (Equality.sort Datatypes_nat__canonical__eqtype_Equality)) (k : nat),
       [seq ρ <- range 0 k | ρ \in [:: x, x & xs]] = [seq ρ <- range 0 k | ρ \in x :: xs]
```

## Lean

```lean
Prosa.Util.List.range_filter_2cons : ∀ (x : ℕ) (xs : List ℕ) (k : ℕ),
  List.filter (fun ρ => decide (ρ ∈ x :: x :: xs)) (Prosa.Util.List.range 0 k) =
    List.filter (fun ρ => decide (ρ ∈ x :: xs)) (Prosa.Util.List.range 0 k)
```

## Lean, imported into Rocq

```coq
Prosa_Util_List_range_filter_2cons
     : forall (x : Nat) (xs : List_inst1 Nat) (k : Nat),
       @eq (List_inst1 Nat)
         (List_filter_inst1 Nat
            (fun _UU03c1_ : Nat =>
             Decidable_decide
               (Membership_mem_inst3 Nat (List_inst1 Nat) (List_instMembership_inst1 Nat)
                  (List_cons_inst1 Nat x (List_cons_inst1 Nat x xs)) _UU03c1_)
               (List_instDecidableMemOfLawfulBEq_inst1 Nat
                  (instBEqOfDecidableEq_inst1 Nat instDecidableEqNat) Nat_instLawfulBEq _UU03c1_
                  (List_cons_inst1 Nat x (List_cons_inst1 Nat x xs))))
            (Prosa_Util_List_range (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0)) k))
         (List_filter_inst1 Nat
            (fun _UU03c1_ : Nat =>
             Decidable_decide
               (Membership_mem_inst3 Nat (List_inst1 Nat) (List_instMembership_inst1 Nat)
                  (List_cons_inst1 Nat x xs) _UU03c1_)
               (List_instDecidableMemOfLawfulBEq_inst1 Nat
                  (instBEqOfDecidableEq_inst1 Nat instDecidableEqNat) Nat_instLawfulBEq _UU03c1_
                  (List_cons_inst1 Nat x xs)))
            (Prosa_Util_List_range (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0)) k))
```
