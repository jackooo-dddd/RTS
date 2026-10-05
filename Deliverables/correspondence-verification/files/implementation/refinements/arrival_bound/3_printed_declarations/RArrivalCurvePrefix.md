# `RArrivalCurvePrefix`

- Kind (Rocq): Definition
- Rocq: `prosa.implementation.refinements.arrival_bound.RArrivalCurvePrefix`
- Lean: `Prosa.Implementation.Refinements.ArrivalBound.RArrivalCurvePrefix`
- Certificate: `RArrivalCurvePrefix_correspondence`

## Official Rocq

```coq
RArrivalCurvePrefix : ArrivalCurvePrefix -> N * seq (N * N) -> Type

RArrivalCurvePrefix is not universe polymorphic
RArrivalCurvePrefix is transparent
Expands to: Constant prosa.implementation.refinements.arrival_bound.RArrivalCurvePrefix
Declared in library prosa.implementation.refinements.arrival_bound, line 112, characters 11-30
RArrivalCurvePrefix
     : ArrivalCurvePrefix -> N * seq (N * N) -> Type
```

Body:

```coq
RArrivalCurvePrefix =
@fun_hrel ArrivalCurvePrefix (N * seq (N * N)) ACPrefixT_to_ACPrefix
     : ArrivalCurvePrefix -> N * seq (N * N) -> Type
```

## Lean

```lean
Prosa.Implementation.Refinements.ArrivalBound.RArrivalCurvePrefix : Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.ArrivalCurvePrefix →
  Prosa.Implementation.Refinements.Refinements.N ×
      List (Prosa.Implementation.Refinements.Refinements.N × Prosa.Implementation.Refinements.Refinements.N) →
    Type
```

Body:

```lean
def Prosa.Implementation.Refinements.ArrivalBound.RArrivalCurvePrefix : Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.ArrivalCurvePrefix →
  Prosa.Implementation.Refinements.Refinements.N ×
      List (Prosa.Implementation.Refinements.Refinements.N × Prosa.Implementation.Refinements.Refinements.N) →
    Type :=
Prosa.Implementation.Refinements.Refinements.fun_hrel
  Prosa.Implementation.Refinements.ArrivalBound.ACPrefixT_to_ACPrefix
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_ArrivalBound_RArrivalCurvePrefix
     : Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_ArrivalCurvePrefix ->
       Prod_inst3 Prosa_Implementation_Refinements_Refinements_N
         (List_inst1
            (Prod_inst3 Prosa_Implementation_Refinements_Refinements_N
               Prosa_Implementation_Refinements_Refinements_N)) ->
       Type
```

Body:

```coq
Prosa_Implementation_Refinements_ArrivalBound_RArrivalCurvePrefix@{} =
Prosa_Implementation_Refinements_Refinements_fun_hrel
  Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_ArrivalCurvePrefix
  (Prod_inst3 Prosa_Implementation_Refinements_Refinements_N
     (List_inst1
        (Prod_inst3 Prosa_Implementation_Refinements_Refinements_N
           Prosa_Implementation_Refinements_Refinements_N)))
  Prosa_Implementation_Refinements_ArrivalBound_ACPrefixT_to_ACPrefix
     : Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_ArrivalCurvePrefix ->
       Prod_inst3 Prosa_Implementation_Refinements_Refinements_N
         (List_inst1
            (Prod_inst3 Prosa_Implementation_Refinements_Refinements_N
               Prosa_Implementation_Refinements_Refinements_N)) ->
       Type

Arguments Prosa_Implementation_Refinements_ArrivalBound_RArrivalCurvePrefix a____at____internal__hyg0
  a____at____internal__hyg0
```
