# `ACPrefixT_to_ACPrefix`

- Kind (Rocq): Definition
- Rocq: `prosa.implementation.refinements.arrival_bound.ACPrefixT_to_ACPrefix`
- Lean: `Prosa.Implementation.Refinements.ArrivalBound.ACPrefixT_to_ACPrefix`
- Certificate: `ACPrefixT_to_ACPrefix_correspondence`

## Official Rocq

```coq
ACPrefixT_to_ACPrefix : N * seq (N * N) -> ArrivalCurvePrefix

ACPrefixT_to_ACPrefix is not universe polymorphic
Arguments ACPrefixT_to_ACPrefix ac_prefix_vec_T
ACPrefixT_to_ACPrefix is transparent
Expands to: Constant prosa.implementation.refinements.arrival_bound.ACPrefixT_to_ACPrefix
Declared in library prosa.implementation.refinements.arrival_bound, line 108, characters 11-32
ACPrefixT_to_ACPrefix
     : N * seq (N * N) -> ArrivalCurvePrefix
```

Body:

```coq
ACPrefixT_to_ACPrefix =
fun ac_prefix_vec_T : N * seq (N * N) =>
(nat_of_bin (@horizon_of_T N ac_prefix_vec_T), m_tb2tn (@steps_of_T N ac_prefix_vec_T))
     : N * seq (N * N) -> ArrivalCurvePrefix

Arguments ACPrefixT_to_ACPrefix ac_prefix_vec_T
```

## Lean

```lean
Prosa.Implementation.Refinements.ArrivalBound.ACPrefixT_to_ACPrefix : Prosa.Implementation.Refinements.Refinements.N ×
    List (Prosa.Implementation.Refinements.Refinements.N × Prosa.Implementation.Refinements.Refinements.N) →
  Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.ArrivalCurvePrefix
```

Body:

```lean
def Prosa.Implementation.Refinements.ArrivalBound.ACPrefixT_to_ACPrefix : Prosa.Implementation.Refinements.Refinements.N ×
    List (Prosa.Implementation.Refinements.Refinements.N × Prosa.Implementation.Refinements.Refinements.N) →
  Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.ArrivalCurvePrefix :=
fun ac_prefix_vec_T =>
  (Prosa.Implementation.Refinements.Refinements.nat_of_bin
      (Prosa.Implementation.Refinements.ArrivalBound.horizon_of_T ac_prefix_vec_T),
    Prosa.Implementation.Refinements.Refinements.m_tb2tn
      (Prosa.Implementation.Refinements.ArrivalBound.steps_of_T ac_prefix_vec_T))
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_ArrivalBound_ACPrefixT_to_ACPrefix
     : Prod_inst3 Prosa_Implementation_Refinements_Refinements_N
         (List_inst1
            (Prod_inst3 Prosa_Implementation_Refinements_Refinements_N
               Prosa_Implementation_Refinements_Refinements_N)) ->
       Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_ArrivalCurvePrefix
```

Body:

```coq
Prosa_Implementation_Refinements_ArrivalBound_ACPrefixT_to_ACPrefix@{} =
fun
  ac_prefix_vec_T : Prod_inst3 Prosa_Implementation_Refinements_Refinements_N
                      (List_inst1
                         (Prod_inst3 Prosa_Implementation_Refinements_Refinements_N
                            Prosa_Implementation_Refinements_Refinements_N)) =>
Prod_mk_inst3 Prosa_Behavior_Time_duration (List_inst1 (Prod_inst3 Prosa_Behavior_Time_duration Nat))
  (Prosa_Implementation_Refinements_Refinements_nat_of_bin
     (Prosa_Implementation_Refinements_ArrivalBound_horizon_of_T
        Prosa_Implementation_Refinements_Refinements_N ac_prefix_vec_T))
  (Prosa_Implementation_Refinements_Refinements_m_tb2tn
     (Prosa_Implementation_Refinements_ArrivalBound_steps_of_T Prosa_Implementation_Refinements_Refinements_N
        ac_prefix_vec_T))
     : Prod_inst3 Prosa_Implementation_Refinements_Refinements_N
         (List_inst1
            (Prod_inst3 Prosa_Implementation_Refinements_Refinements_N
               Prosa_Implementation_Refinements_Refinements_N)) ->
       Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_ArrivalCurvePrefix

Arguments Prosa_Implementation_Refinements_ArrivalBound_ACPrefixT_to_ACPrefix ac_prefix_vec_T
```
