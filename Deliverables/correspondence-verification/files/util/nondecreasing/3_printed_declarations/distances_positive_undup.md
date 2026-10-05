# `distances_positive_undup`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.nondecreasing.distances_positive_undup`
- Lean: `Prosa.Util.Nondecreasing.distances_positive_undup`
- Certificate: `distances_positive_undup_correspondence_certificate`

## Official Rocq

```coq
distances_positive_undup :
forall xs : seq nat,
nondecreasing_sequence xs ->

distances_positive_undup is not universe polymorphic
Arguments distances_positive_undup xs%seq_scope _
distances_positive_undup is opaque
Expands to: Constant prosa.util.nondecreasing.distances_positive_undup
Declared in library prosa.util.nondecreasing, line 740, characters 8-32
distances_positive_undup
     : forall xs : seq nat,
       nondecreasing_sequence xs ->
       [seq d <- distances xs | 0 < d] = distances (@undup Datatypes_nat__canonical__eqtype_Equality xs)
```

## Lean

```lean
Prosa.Util.Nondecreasing.distances_positive_undup : ∀ (xs : List ℕ),
  Prosa.Util.Nondecreasing.nondecreasing_sequence xs →
    List.filter (fun x => decide (x > 0)) (Prosa.Util.Nondecreasing.distances xs) =
      Prosa.Util.Nondecreasing.distances xs.dedup
```

## Lean, imported into Rocq

```coq
Prosa_Util_Nondecreasing_distances_positive_undup
     : forall xs : List_inst1 Nat,
       Prosa_Util_Nondecreasing_nondecreasing_sequence xs ->
       @eq (List_inst1 Nat)
         (List_filter_inst1 Nat
            (fun x____at___Prosa_Util_Nondecreasing2635657019__hygCtx__hyg61 : Nat =>
             Decidable_decide
               (GT_gt_inst1 Nat instLTNat x____at___Prosa_Util_Nondecreasing2635657019__hygCtx__hyg61
                  (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0)))
               (Nat_decLt (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0))
                  x____at___Prosa_Util_Nondecreasing2635657019__hygCtx__hyg61))
            (Prosa_Util_Nondecreasing_distances xs))
         (Prosa_Util_Nondecreasing_distances (List_dedup_inst1 Nat instDecidableEqNat xs))
```
