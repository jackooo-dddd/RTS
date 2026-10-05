# `ACPrefix_to_ACPrefixT`

- Kind (Rocq): Definition
- Rocq: `prosa.implementation.refinements.arrival_bound.ACPrefix_to_ACPrefixT`
- Lean: `Prosa.Implementation.Refinements.ArrivalBound.ACPrefix_to_ACPrefixT`
- Certificate: `ACPrefix_to_ACPrefixT_correspondence`

## Official Rocq

```coq
ACPrefix_to_ACPrefixT : ArrivalCurvePrefix -> N * seq (N * N)

ACPrefix_to_ACPrefixT is not universe polymorphic
Arguments ACPrefix_to_ACPrefixT ac_prefix_vec
ACPrefix_to_ACPrefixT is transparent
Expands to: Constant prosa.implementation.refinements.arrival_bound.ACPrefix_to_ACPrefixT
Declared in library prosa.implementation.refinements.arrival_bound, line 116, characters 11-32
ACPrefix_to_ACPrefixT
     : ArrivalCurvePrefix -> N * seq (N * N)
```

Body:

```coq
ACPrefix_to_ACPrefixT =
fun ac_prefix_vec : ArrivalCurvePrefix =>
(bin_of_nat (horizon_of ac_prefix_vec), m_tn2tb (steps_of ac_prefix_vec))
     : ArrivalCurvePrefix -> N * seq (N * N)

Arguments ACPrefix_to_ACPrefixT ac_prefix_vec
```

## Lean

```lean
Prosa.Implementation.Refinements.ArrivalBound.ACPrefix_to_ACPrefixT : Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.ArrivalCurvePrefix →
  Prosa.Implementation.Refinements.Refinements.N ×
    List (Prosa.Implementation.Refinements.Refinements.N × Prosa.Implementation.Refinements.Refinements.N)
```

Body:

```lean
def Prosa.Implementation.Refinements.ArrivalBound.ACPrefix_to_ACPrefixT : Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.ArrivalCurvePrefix →
  Prosa.Implementation.Refinements.Refinements.N ×
    List (Prosa.Implementation.Refinements.Refinements.N × Prosa.Implementation.Refinements.Refinements.N) :=
fun ac_prefix_vec =>
  (Prosa.Implementation.Refinements.Refinements.bin_of_nat
      (Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.horizon_of ac_prefix_vec),
    Prosa.Implementation.Refinements.Refinements.m_tn2tb
      (Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.steps_of ac_prefix_vec))
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_ArrivalBound_ACPrefix_to_ACPrefixT
     : Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_ArrivalCurvePrefix ->
       Prod_inst3 Prosa_Implementation_Refinements_Refinements_N
         (List_inst1
            (Prod_inst3 Prosa_Implementation_Refinements_Refinements_N
               Prosa_Implementation_Refinements_Refinements_N))
```

Body:

```coq
Prosa_Implementation_Refinements_ArrivalBound_ACPrefix_to_ACPrefixT@{} =
fun ac_prefix_vec : Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_ArrivalCurvePrefix =>
Prod_mk_inst3 Prosa_Implementation_Refinements_Refinements_N
  (List_inst1
     (Prod_inst3 Prosa_Implementation_Refinements_Refinements_N
        Prosa_Implementation_Refinements_Refinements_N))
  (Prosa_Implementation_Refinements_Refinements_bin_of_nat
     (Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_horizon_of ac_prefix_vec))
  (Prosa_Implementation_Refinements_Refinements_m_tn2tb
     (Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_steps_of ac_prefix_vec))
     : Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_ArrivalCurvePrefix ->
       Prod_inst3 Prosa_Implementation_Refinements_Refinements_N
         (List_inst1
            (Prod_inst3 Prosa_Implementation_Refinements_Refinements_N
               Prosa_Implementation_Refinements_Refinements_N))

Arguments Prosa_Implementation_Refinements_ArrivalBound_ACPrefix_to_ACPrefixT ac_prefix_vec
```
