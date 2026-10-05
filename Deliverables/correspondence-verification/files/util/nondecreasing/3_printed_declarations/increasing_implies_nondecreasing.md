# `increasing_implies_nondecreasing`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.nondecreasing.increasing_implies_nondecreasing`
- Lean: `Prosa.Util.Nondecreasing.increasing_implies_nondecreasing`
- Certificate: `increasing_implies_nondecreasing_correspondence_certificate`

## Official Rocq

```coq
increasing_implies_nondecreasing : forall xs : seq nat, increasing_sequence xs -> nondecreasing_sequence xs

increasing_implies_nondecreasing is not universe polymorphic
Arguments increasing_implies_nondecreasing xs%seq_scope _ n1 n2 _
increasing_implies_nondecreasing is opaque
Expands to: Constant prosa.util.nondecreasing.increasing_implies_nondecreasing
Declared in library prosa.util.nondecreasing, line 73, characters 8-40
increasing_implies_nondecreasing
     : forall xs : seq nat, increasing_sequence xs -> nondecreasing_sequence xs
```

## Lean

```lean
Prosa.Util.Nondecreasing.increasing_implies_nondecreasing : ∀ (xs : List ℕ),
  Prosa.Util.Nondecreasing.increasing_sequence xs → Prosa.Util.Nondecreasing.nondecreasing_sequence xs
```

## Lean, imported into Rocq

```coq
Prosa_Util_Nondecreasing_increasing_implies_nondecreasing
     : forall xs : List_inst1 Nat,
       Prosa_Util_Nondecreasing_increasing_sequence xs -> Prosa_Util_Nondecreasing_nondecreasing_sequence xs
```
