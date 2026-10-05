# `leq_stepsT_is_transitive`

- Kind (Rocq): Lemma
- Rocq: `prosa.implementation.refinements.arrival_bound.leq_stepsT_is_transitive`
- Lean: `Prosa.Implementation.Refinements.ArrivalBound.leq_stepsT_is_transitive`
- Certificate: `leq_stepsT_is_transitive_correspondence`

## Official Rocq

```coq
leq_stepsT_is_transitive : @transitive (N * N) (@leq_steps_T N leq_N)

leq_stepsT_is_transitive is not universe polymorphic
Arguments leq_stepsT_is_transitive y x z _ _
leq_stepsT_is_transitive is opaque
Expands to: Constant prosa.implementation.refinements.arrival_bound.leq_stepsT_is_transitive
Declared in library prosa.implementation.refinements.arrival_bound, line 142, characters 6-30
leq_stepsT_is_transitive
     : @transitive (N * N) (@leq_steps_T N leq_N)
```

## Lean

```lean
Prosa.Implementation.Refinements.ArrivalBound.leq_stepsT_is_transitive : ∀
  (y x z : Prosa.Implementation.Refinements.Refinements.N × Prosa.Implementation.Refinements.Refinements.N),
  Prosa.Implementation.Refinements.ArrivalBound.leq_steps_T x y = true →
    Prosa.Implementation.Refinements.ArrivalBound.leq_steps_T y z = true →
      Prosa.Implementation.Refinements.ArrivalBound.leq_steps_T x z = true
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_ArrivalBound_leq_stepsT_is_transitive
     : forall
         y x
          z : Prod_inst3 Prosa_Implementation_Refinements_Refinements_N
                Prosa_Implementation_Refinements_Refinements_N,
       @eq Bool
         (Prosa_Implementation_Refinements_ArrivalBound_leq_steps_T
            Prosa_Implementation_Refinements_Refinements_N Prosa_Implementation_Refinements_Refinements_leq_N
            x y)
         Bool_true ->
       @eq Bool
         (Prosa_Implementation_Refinements_ArrivalBound_leq_steps_T
            Prosa_Implementation_Refinements_Refinements_N Prosa_Implementation_Refinements_Refinements_leq_N
            y z)
         Bool_true ->
       @eq Bool
         (Prosa_Implementation_Refinements_ArrivalBound_leq_steps_T
            Prosa_Implementation_Refinements_Refinements_N Prosa_Implementation_Refinements_Refinements_leq_N
            x z)
         Bool_true
```
