# `ltn_stepsT_is_transitive`

- Kind (Rocq): Lemma
- Rocq: `prosa.implementation.refinements.arrival_bound.ltn_stepsT_is_transitive`
- Lean: `Prosa.Implementation.Refinements.ArrivalBound.ltn_stepsT_is_transitive`
- Certificate: `ltn_stepsT_is_transitive_correspondence`

## Official Rocq

```coq
ltn_stepsT_is_transitive : @transitive (N * N) (@ltn_steps_T N lt_N)

ltn_stepsT_is_transitive is not universe polymorphic
Arguments ltn_stepsT_is_transitive y x z _ _
ltn_stepsT_is_transitive is opaque
Expands to: Constant prosa.implementation.refinements.arrival_bound.ltn_stepsT_is_transitive
Declared in library prosa.implementation.refinements.arrival_bound, line 158, characters 6-30
ltn_stepsT_is_transitive
     : @transitive (N * N) (@ltn_steps_T N lt_N)
```

## Lean

```lean
Prosa.Implementation.Refinements.ArrivalBound.ltn_stepsT_is_transitive : ∀
  (y x z : Prosa.Implementation.Refinements.Refinements.N × Prosa.Implementation.Refinements.Refinements.N),
  Prosa.Implementation.Refinements.ArrivalBound.ltn_steps_T x y = true →
    Prosa.Implementation.Refinements.ArrivalBound.ltn_steps_T y z = true →
      Prosa.Implementation.Refinements.ArrivalBound.ltn_steps_T x z = true
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_ArrivalBound_ltn_stepsT_is_transitive
     : forall
         y x
          z : Prod_inst3 Prosa_Implementation_Refinements_Refinements_N
                Prosa_Implementation_Refinements_Refinements_N,
       @eq Bool
         (Prosa_Implementation_Refinements_ArrivalBound_ltn_steps_T
            Prosa_Implementation_Refinements_Refinements_N Prosa_Implementation_Refinements_Refinements_lt_N
            x y)
         Bool_true ->
       @eq Bool
         (Prosa_Implementation_Refinements_ArrivalBound_ltn_steps_T
            Prosa_Implementation_Refinements_Refinements_N Prosa_Implementation_Refinements_Refinements_lt_N
            y z)
         Bool_true ->
       @eq Bool
         (Prosa_Implementation_Refinements_ArrivalBound_ltn_steps_T
            Prosa_Implementation_Refinements_Refinements_N Prosa_Implementation_Refinements_Refinements_lt_N
            x z)
         Bool_true
```
