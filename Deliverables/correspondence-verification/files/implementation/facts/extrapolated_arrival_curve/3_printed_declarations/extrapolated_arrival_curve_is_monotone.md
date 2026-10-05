# `extrapolated_arrival_curve_is_monotone`

- Kind (Rocq): Lemma
- Rocq: `prosa.implementation.facts.extrapolated_arrival_curve.extrapolated_arrival_curve_is_monotone`
- Lean: `Prosa.Implementation.Facts.ExtrapolatedArrivalCurve.extrapolated_arrival_curve_is_monotone`
- Certificate: `facts_extrapolated_arrival_curve_is_monotone_certificate`

## Official Rocq

```coq
extrapolated_arrival_curve_is_monotone :
forall ac_prefix : ArrivalCurvePrefix,
is_true (positive_horizon ac_prefix) ->
is_true (sorted_leq_steps ac_prefix) -> @monotone nat leq (extrapolated_arrival_curve ac_prefix)

extrapolated_arrival_curve_is_monotone is not universe polymorphic
Arguments extrapolated_arrival_curve_is_monotone ac_prefix H_positive H_sorted_leq x y _
extrapolated_arrival_curve_is_monotone is opaque
Expands to: Constant
            prosa.implementation.facts.extrapolated_arrival_curve.extrapolated_arrival_curve_is_monotone
Declared in library prosa.implementation.facts.extrapolated_arrival_curve, line 202, characters 8-46
extrapolated_arrival_curve_is_monotone
     : forall ac_prefix : ArrivalCurvePrefix,
       is_true (positive_horizon ac_prefix) ->
       is_true (sorted_leq_steps ac_prefix) -> @monotone nat leq (extrapolated_arrival_curve ac_prefix)
```

## Lean

```lean
Prosa.Implementation.Facts.ExtrapolatedArrivalCurve.extrapolated_arrival_curve_is_monotone : ∀
  (ac_prefix : Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.ArrivalCurvePrefix),
  Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.positive_horizon ac_prefix = true →
    Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.sorted_leq_steps ac_prefix = true →
      ∀ (t1 t2 : ℕ),
        t1 ≤ t2 →
          Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.extrapolated_arrival_curve ac_prefix t1 ≤
            Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.extrapolated_arrival_curve ac_prefix t2
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Facts_ExtrapolatedArrivalCurve_extrapolated_arrival_curve_is_monotone
     : forall ac_prefix : Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_ArrivalCurvePrefix,
       @eq Bool (Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_positive_horizon ac_prefix)
         Bool_true ->
       @eq Bool (Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_sorted_leq_steps ac_prefix)
         Bool_true ->
       forall t1 t2 : Nat,
       LE_le_inst1 Nat instLENat t1 t2 ->
       LE_le_inst1 Nat instLENat
         (Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_extrapolated_arrival_curve ac_prefix t1)
         (Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_extrapolated_arrival_curve ac_prefix t2)
```
