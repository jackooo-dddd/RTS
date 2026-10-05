# `lcm_seq_divides_lcm_super`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.lcmseq.lcm_seq_divides_lcm_super`
- Lean: `Prosa.Util.Lcmseq.lcm_seq_divides_lcm_super`
- Certificate: `lcm_seq_divides_lcm_super_correspondence`

## Official Rocq

```coq
lcm_seq_divides_lcm_super : forall (x : nat) (xs : seq nat), is_true (lcml xs %| lcml (x :: xs))

lcm_seq_divides_lcm_super is not universe polymorphic
Arguments lcm_seq_divides_lcm_super x%nat_scope xs%seq_scope
lcm_seq_divides_lcm_super is opaque
Expands to: Constant prosa.util.lcmseq.lcm_seq_divides_lcm_super
Declared in library prosa.util.lcmseq, line 19, characters 6-31
lcm_seq_divides_lcm_super
     : forall (x : nat) (xs : seq nat), is_true (lcml xs %| lcml (x :: xs))
```

## Lean

```lean
Prosa.Util.Lcmseq.lcm_seq_divides_lcm_super : ∀ (x : ℕ) (xs : List ℕ),
  Prosa.Util.Lcmseq.lcml xs ∣ Prosa.Util.Lcmseq.lcml (x :: xs)
```

## Lean, imported into Rocq

```coq
Prosa_Util_Lcmseq_lcm_seq_divides_lcm_super
     : forall (x : Nat) (xs : List_inst1 Nat),
       Dvd_dvd_inst1 Nat Nat_instDvd (Prosa_Util_Lcmseq_lcml xs)
         (Prosa_Util_Lcmseq_lcml (List_cons_inst1 Nat x xs))
```
