# `sorted_ltn_steps_imply_sorted_leq_steps_steps`

- Kind (Rocq): Lemma
- Rocq: `prosa.implementation.facts.extrapolated_arrival_curve.sorted_ltn_steps_imply_sorted_leq_steps_steps`
- Lean: `Prosa.Implementation.Facts.ExtrapolatedArrivalCurve.sorted_ltn_steps_imply_sorted_leq_steps_steps`
- Certificate: `facts_sorted_ltn_implies_sorted_leq_certificate`

## Official Rocq

```coq
sorted_ltn_steps_imply_sorted_leq_steps_steps :
forall ac_prefix : ArrivalCurvePrefix,
is_true (sorted_ltn_steps ac_prefix) ->
is_true (no_inf_arrivals ac_prefix) -> is_true (sorted_leq_steps ac_prefix)

sorted_ltn_steps_imply_sorted_leq_steps_steps is not universe polymorphic
Arguments sorted_ltn_steps_imply_sorted_leq_steps_steps ac_prefix H_sorted_ltn H_no_inf_arrivals
sorted_ltn_steps_imply_sorted_leq_steps_steps is opaque
Expands to: Constant
            prosa.implementation.facts.extrapolated_arrival_curve.sorted_ltn_steps_imply_sorted_leq_steps_steps
Declared in library prosa.implementation.facts.extrapolated_arrival_curve, line 138, characters 8-53
sorted_ltn_steps_imply_sorted_leq_steps_steps
     : forall ac_prefix : ArrivalCurvePrefix,
       is_true (sorted_ltn_steps ac_prefix) ->
       is_true (no_inf_arrivals ac_prefix) -> is_true (sorted_leq_steps ac_prefix)
```

## Lean

```lean
Prosa.Implementation.Facts.ExtrapolatedArrivalCurve.sorted_ltn_steps_imply_sorted_leq_steps_steps : ∀
  (ac_prefix : Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.ArrivalCurvePrefix),
  Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.sorted_ltn_steps ac_prefix = true →
    Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.no_inf_arrivals ac_prefix = true →
      Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.sorted_leq_steps ac_prefix = true
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Facts_ExtrapolatedArrivalCurve_sorted_ltn_steps_imply_sorted_leq_steps_steps
     : forall ac_prefix : Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_ArrivalCurvePrefix,
       @eq Bool (Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_sorted_ltn_steps ac_prefix)
         Bool_true ->
       @eq Bool (Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_no_inf_arrivals ac_prefix)
         Bool_true ->
       @eq Bool (Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_sorted_leq_steps ac_prefix)
         Bool_true
```
