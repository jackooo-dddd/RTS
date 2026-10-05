# `nondec_seq_zero_first`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.nondecreasing.nondec_seq_zero_first`
- Lean: `Prosa.Util.Nondecreasing.nondec_seq_zero_first`
- Certificate: `nondec_seq_zero_first_correspondence_certificate`

## Official Rocq

```coq
nondec_seq_zero_first :
forall xs : @pred_sort nat (seq_predType Datatypes_nat__canonical__eqtype_Equality),
is_true (0 \in xs) -> nondecreasing_sequence xs -> first0 xs = 0

nondec_seq_zero_first is not universe polymorphic
Arguments nondec_seq_zero_first xs _ _
nondec_seq_zero_first is opaque
Expands to: Constant prosa.util.nondecreasing.nondec_seq_zero_first
Declared in library prosa.util.nondecreasing, line 88, characters 8-29
nondec_seq_zero_first
     : forall xs : @pred_sort nat (seq_predType Datatypes_nat__canonical__eqtype_Equality),
       is_true (0 \in xs) -> nondecreasing_sequence xs -> first0 xs = 0
```

## Lean

```lean
Prosa.Util.Nondecreasing.nondec_seq_zero_first : ∀ (xs : List ℕ),
  0 ∈ xs → Prosa.Util.Nondecreasing.nondecreasing_sequence xs → Prosa.Util.List.first0 xs = 0
```

## Lean, imported into Rocq

```coq
Prosa_Util_Nondecreasing_nondec_seq_zero_first
     : forall xs : List_inst1 Nat,
       Membership_mem_inst3 Nat (List_inst1 Nat) (List_instMembership_inst1 Nat) xs
         (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0)) ->
       Prosa_Util_Nondecreasing_nondecreasing_sequence xs ->
       @eq Nat (Prosa_Util_List_first0 xs) (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0))
```
