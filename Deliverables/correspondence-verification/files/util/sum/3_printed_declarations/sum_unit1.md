# `sum_unit1`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.sum.sum_unit1`
- Lean: `Prosa.Util.Sum.sum_unit1`
- Certificate: `sum_unit1_statement_certificate`

## Official Rocq

```coq
sum_unit1 :
forall {F : unit -> nat},
@bigop.bigop.body nat (fintype.Finite.sort fintype.Datatypes_unit__canonical__fintype_Finite) 0
  (bigop.index_enum fintype.Datatypes_unit__canonical__fintype_Finite)
  (fun r : fintype.Finite.sort fintype.Datatypes_unit__canonical__fintype_Finite =>
   @bigop.BigBody nat (fintype.Finite.sort fintype.Datatypes_unit__canonical__fintype_Finite) r addn true
     (F r)) =
F tt

sum_unit1 is not universe polymorphic
Arguments sum_unit1 {F}%function_scope
sum_unit1 is opaque
Expands to: Constant prosa.util.sum.sum_unit1
Declared in library prosa.util.sum, line 446, characters 6-15
@sum_unit1
     : forall F : unit -> nat,
       @bigop.bigop.body nat (fintype.Finite.sort fintype.Datatypes_unit__canonical__fintype_Finite) 0
         (bigop.index_enum fintype.Datatypes_unit__canonical__fintype_Finite)
         (fun r : fintype.Finite.sort fintype.Datatypes_unit__canonical__fintype_Finite =>
          @bigop.BigBody nat (fintype.Finite.sort fintype.Datatypes_unit__canonical__fintype_Finite) r addn
            true (F r)) =
       F tt
```

## Lean

```lean
Prosa.Util.Sum.sum_unit1 : ∀ (F : Unit → ℕ), ∑ r, F r = F ()
```

## Lean, imported into Rocq

```coq
Prosa_Util_Sum_sum_unit1
     : forall F : ImportedSumSequence.Unit -> Nat,
       @eq Nat
         (Finset_sum_inst3 ImportedSumSequence.Unit Nat Nat_instAddCommMonoid
            (Finset_univ_inst1 ImportedSumSequence.Unit PUnit_fintype_inst1)
            (fun r : ImportedSumSequence.Unit => F r))
         (F ImportedSumSequence.Unit_unit)
```
