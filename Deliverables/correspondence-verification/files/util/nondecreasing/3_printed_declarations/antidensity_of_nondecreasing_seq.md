# `antidensity_of_nondecreasing_seq`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.nondecreasing.antidensity_of_nondecreasing_seq`
- Lean: `Prosa.Util.Nondecreasing.antidensity_of_nondecreasing_seq`
- Certificate: `antidensity_of_nondecreasing_seq_correspondence_certificate`

## Official Rocq

```coq
antidensity_of_nondecreasing_seq :
forall (xs : seq nat) (x n : nat),
nondecreasing_sequence xs -> is_true (@nth nat 0 xs n < x < @nth nat 0 xs n.+1) -> is_true (x \notin xs)

antidensity_of_nondecreasing_seq is not universe polymorphic
Arguments antidensity_of_nondecreasing_seq xs%seq_scope (x n)%nat_scope _ _
antidensity_of_nondecreasing_seq is opaque
Expands to: Constant prosa.util.nondecreasing.antidensity_of_nondecreasing_seq
Declared in library prosa.util.nondecreasing, line 204, characters 8-40
antidensity_of_nondecreasing_seq
     : forall (xs : seq nat) (x n : nat),
       nondecreasing_sequence xs ->
       is_true (@nth nat 0 xs n < x < @nth nat 0 xs n.+1) -> is_true (x \notin xs)
```

## Lean

```lean
Prosa.Util.Nondecreasing.antidensity_of_nondecreasing_seq : ∀ (xs : List ℕ) (x n : ℕ),
  Prosa.Util.Nondecreasing.nondecreasing_sequence xs →
    Prosa.Util.Nondecreasing.nthD✝ xs n < x ∧ x < Prosa.Util.Nondecreasing.nthD✝ xs (n + 1) → x ∉ xs
```

## Lean, imported into Rocq

```coq
Prosa_Util_Nondecreasing_antidensity_of_nondecreasing_seq
     : forall (xs : List_inst1 Nat) (x n : Nat),
       Prosa_Util_Nondecreasing_nondecreasing_sequence xs ->
       And
         (LT_lt_inst1 Nat instLTNat (_private_Prosa_Util_Nondecreasing0_Prosa_Util_Nondecreasing_nthD xs n) x)
         (LT_lt_inst1 Nat instLTNat x
            (_private_Prosa_Util_Nondecreasing0_Prosa_Util_Nondecreasing_nthD xs
               (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat) n
                  (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1))))) ->
       Not (Membership_mem_inst3 Nat (List_inst1 Nat) (List_instMembership_inst1 Nat) xs x)
```
