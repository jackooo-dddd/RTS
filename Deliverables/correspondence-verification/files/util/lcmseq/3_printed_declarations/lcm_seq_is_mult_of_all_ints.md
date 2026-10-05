# `lcm_seq_is_mult_of_all_ints`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.lcmseq.lcm_seq_is_mult_of_all_ints`
- Lean: `Prosa.Util.Lcmseq.lcm_seq_is_mult_of_all_ints`
- Certificate: `lcm_seq_is_mult_of_all_ints_correspondence`

## Official Rocq

```coq
lcm_seq_is_mult_of_all_ints : forall (x : nat) (xs : seq nat), is_true (x \in xs) -> is_true (x %| lcml xs)

lcm_seq_is_mult_of_all_ints is not universe polymorphic
Arguments lcm_seq_is_mult_of_all_ints x%nat_scope xs%seq_scope _
lcm_seq_is_mult_of_all_ints is opaque
Expands to: Constant prosa.util.lcmseq.lcm_seq_is_mult_of_all_ints
Declared in library prosa.util.lcmseq, line 29, characters 6-33
lcm_seq_is_mult_of_all_ints
     : forall (x : nat) (xs : seq nat), is_true (x \in xs) -> is_true (x %| lcml xs)
```

## Lean

```lean
Prosa.Util.Lcmseq.lcm_seq_is_mult_of_all_ints : ∀ (x : ℕ) (xs : List ℕ), x ∈ xs → x ∣ Prosa.Util.Lcmseq.lcml xs
```

## Lean, imported into Rocq

```coq
Prosa_Util_Lcmseq_lcm_seq_is_mult_of_all_ints
     : forall (x : Nat) (xs : List_inst1 Nat),
       Membership_mem_inst3 Nat (List_inst1 Nat) (List_instMembership_inst1 Nat) xs x ->
       Dvd_dvd_inst1 Nat Nat_instDvd x (Prosa_Util_Lcmseq_lcml xs)
```
