# `last0_undup`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.nondecreasing.last0_undup`
- Lean: `Prosa.Util.Nondecreasing.last0_undup`
- Certificate: `last0_undup_correspondence_certificate`

## Official Rocq

```coq
last0_undup :
forall xs : seq nat,
nondecreasing_sequence xs -> last0 (@undup Datatypes_nat__canonical__eqtype_Equality xs) = last0 xs

last0_undup is not universe polymorphic
Arguments last0_undup xs%seq_scope _
last0_undup is opaque
Expands to: Constant prosa.util.nondecreasing.last0_undup
Declared in library prosa.util.nondecreasing, line 345, characters 8-19
last0_undup
     : forall xs : seq nat,
       nondecreasing_sequence xs -> last0 (@undup Datatypes_nat__canonical__eqtype_Equality xs) = last0 xs
```

## Lean

```lean
Prosa.Util.Nondecreasing.last0_undup : ∀ (xs : List ℕ),
  Prosa.Util.Nondecreasing.nondecreasing_sequence xs → Prosa.Util.List.last0 xs.dedup = Prosa.Util.List.last0 xs
```

## Lean, imported into Rocq

```coq
Prosa_Util_Nondecreasing_last0_undup
     : forall xs : List_inst1 Nat,
       Prosa_Util_Nondecreasing_nondecreasing_sequence xs ->
       @eq Nat (Prosa_Util_List_last0 (List_dedup_inst1 Nat instDecidableEqNat xs))
         (Prosa_Util_List_last0 xs)
```
