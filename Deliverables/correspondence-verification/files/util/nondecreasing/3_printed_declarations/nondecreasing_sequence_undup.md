# `nondecreasing_sequence_undup`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.nondecreasing.nondecreasing_sequence_undup`
- Lean: `Prosa.Util.Nondecreasing.nondecreasing_sequence_undup`
- Certificate: `nondecreasing_sequence_undup_correspondence_certificate`

## Official Rocq

```coq
nondecreasing_sequence_undup :
forall xs : seq nat,
nondecreasing_sequence xs -> nondecreasing_sequence (@undup Datatypes_nat__canonical__eqtype_Equality xs)

nondecreasing_sequence_undup is not universe polymorphic
Arguments nondecreasing_sequence_undup xs%seq_scope _ n1 n2 _
nondecreasing_sequence_undup is opaque
Expands to: Constant prosa.util.nondecreasing.nondecreasing_sequence_undup
Declared in library prosa.util.nondecreasing, line 362, characters 8-36
nondecreasing_sequence_undup
     : forall xs : seq nat,
       nondecreasing_sequence xs ->
       nondecreasing_sequence (@undup Datatypes_nat__canonical__eqtype_Equality xs)
```

## Lean

```lean
Prosa.Util.Nondecreasing.nondecreasing_sequence_undup : ∀ (xs : List ℕ),
  Prosa.Util.Nondecreasing.nondecreasing_sequence xs → Prosa.Util.Nondecreasing.nondecreasing_sequence xs.dedup
```

## Lean, imported into Rocq

```coq
Prosa_Util_Nondecreasing_nondecreasing_sequence_undup
     : forall xs : List_inst1 Nat,
       Prosa_Util_Nondecreasing_nondecreasing_sequence xs ->
       Prosa_Util_Nondecreasing_nondecreasing_sequence (List_dedup_inst1 Nat instDecidableEqNat xs)
```
