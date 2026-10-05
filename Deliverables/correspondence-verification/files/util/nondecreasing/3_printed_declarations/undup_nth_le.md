# `undup_nth_le`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.nondecreasing.undup_nth_le`
- Lean: `Prosa.Util.Nondecreasing.undup_nth_le`
- Certificate: `undup_nth_le_correspondence_certificate`

## Official Rocq

```coq
undup_nth_le :
forall xs : seq nat,
nondecreasing_sequence xs ->
is_true
  (@nth nat 0 (@undup Datatypes_nat__canonical__eqtype_Equality xs)
     (@size (Equality.sort Datatypes_nat__canonical__eqtype_Equality)
        (@undup Datatypes_nat__canonical__eqtype_Equality xs)).-2 <=
   @nth nat 0 xs (@size nat xs).-2)

undup_nth_le is not universe polymorphic
Arguments undup_nth_le xs%seq_scope _
undup_nth_le is opaque
Expands to: Constant prosa.util.nondecreasing.undup_nth_le
Declared in library prosa.util.nondecreasing, line 386, characters 8-20
undup_nth_le
     : forall xs : seq nat,
       nondecreasing_sequence xs ->
       is_true
         (@nth nat 0 (@undup Datatypes_nat__canonical__eqtype_Equality xs)
            (@size (Equality.sort Datatypes_nat__canonical__eqtype_Equality)
               (@undup Datatypes_nat__canonical__eqtype_Equality xs)).-2 <=
          @nth nat 0 xs (@size nat xs).-2)
```

## Lean

```lean
Prosa.Util.Nondecreasing.undup_nth_le : ∀ (xs : List ℕ),
  Prosa.Util.Nondecreasing.nondecreasing_sequence xs →
    Prosa.Util.Nondecreasing.nthD✝ xs.dedup (xs.dedup.length - 2) ≤ Prosa.Util.Nondecreasing.nthD✝ xs (xs.length - 2)
```

## Lean, imported into Rocq

```coq
Prosa_Util_Nondecreasing_undup_nth_le
     : forall xs : List_inst1 Nat,
       Prosa_Util_Nondecreasing_nondecreasing_sequence xs ->
       LE_le_inst1 Nat instLENat
         (_private_Prosa_Util_Nondecreasing0_Prosa_Util_Nondecreasing_nthD
            (List_dedup_inst1 Nat instDecidableEqNat xs)
            (HSub_hSub_inst7 Nat Nat Nat (instHSub_inst1 Nat instSubNat)
               (List_length_inst1 Nat (List_dedup_inst1 Nat instDecidableEqNat xs))
               (OfNat_ofNat_inst1 Nat 2 (instOfNatNat 2))))
         (_private_Prosa_Util_Nondecreasing0_Prosa_Util_Nondecreasing_nthD xs
            (HSub_hSub_inst7 Nat Nat Nat (instHSub_inst1 Nat instSubNat) (List_length_inst1 Nat xs)
               (OfNat_ofNat_inst1 Nat 2 (instOfNatNat 2))))
```
