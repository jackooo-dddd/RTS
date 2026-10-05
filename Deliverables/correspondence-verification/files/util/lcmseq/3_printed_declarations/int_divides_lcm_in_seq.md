# `int_divides_lcm_in_seq`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.lcmseq.int_divides_lcm_in_seq`
- Lean: `Prosa.Util.Lcmseq.int_divides_lcm_in_seq`
- Certificate: `int_divides_lcm_in_seq_correspondence`

## Official Rocq

```coq
int_divides_lcm_in_seq : forall (x : nat) (xs : seq nat), is_true (x %| lcml (x :: xs))

int_divides_lcm_in_seq is not universe polymorphic
Arguments int_divides_lcm_in_seq x%nat_scope xs%seq_scope
int_divides_lcm_in_seq is opaque
Expands to: Constant prosa.util.lcmseq.int_divides_lcm_in_seq
Declared in library prosa.util.lcmseq, line 9, characters 6-28
int_divides_lcm_in_seq
     : forall (x : nat) (xs : seq nat), is_true (x %| lcml (x :: xs))
```

## Lean

```lean
Prosa.Util.Lcmseq.int_divides_lcm_in_seq : ∀ (x : ℕ) (xs : List ℕ), x ∣ Prosa.Util.Lcmseq.lcml (x :: xs)
```

## Lean, imported into Rocq

```coq
Prosa_Util_Lcmseq_int_divides_lcm_in_seq
     : forall (x : Nat) (xs : List_inst1 Nat),
       Dvd_dvd_inst1 Nat Nat_instDvd x (Prosa_Util_Lcmseq_lcml (List_cons_inst1 Nat x xs))
```
