# `step_at_0_is_00`

- Kind (Rocq): Lemma
- Rocq: `prosa.implementation.facts.extrapolated_arrival_curve.step_at_0_is_00`
- Lean: `Prosa.Implementation.Facts.ExtrapolatedArrivalCurve.step_at_0_is_00`
- Certificate: `facts_step_at_zero_certificate`

## Official Rocq

```coq
step_at_0_is_00 :
forall ac_prefix : ArrivalCurvePrefix,
is_true (sorted_ltn_steps ac_prefix) -> is_true (no_inf_arrivals ac_prefix) -> step_at ac_prefix 0 = (0, 0)

step_at_0_is_00 is not universe polymorphic
Arguments step_at_0_is_00 ac_prefix H_sorted_ltn H_no_inf_arrivals
step_at_0_is_00 is opaque
Expands to: Constant prosa.implementation.facts.extrapolated_arrival_curve.step_at_0_is_00
Declared in library prosa.implementation.facts.extrapolated_arrival_curve, line 150, characters 8-23
step_at_0_is_00
     : forall ac_prefix : ArrivalCurvePrefix,
       is_true (sorted_ltn_steps ac_prefix) ->
       is_true (no_inf_arrivals ac_prefix) -> step_at ac_prefix 0 = (0, 0)
```

## Lean

```lean
Prosa.Implementation.Facts.ExtrapolatedArrivalCurve.step_at_0_is_00 : ∀
  (ac_prefix : Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.ArrivalCurvePrefix),
  Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.sorted_ltn_steps ac_prefix = true →
    Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.no_inf_arrivals ac_prefix = true →
      Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.step_at ac_prefix 0 = (0, 0)
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Facts_ExtrapolatedArrivalCurve_step_at_0_is_00
     : forall ac_prefix : Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_ArrivalCurvePrefix,
       @eq Bool (Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_sorted_ltn_steps ac_prefix)
         Bool_true ->
       @eq Bool (Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_no_inf_arrivals ac_prefix)
         Bool_true ->
       @eq (Prod_inst3 Prosa_Behavior_Time_duration Nat)
         (Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_step_at ac_prefix
            (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 0 (instOfNatNat 0)))
         (Prod_mk_inst3 Prosa_Behavior_Time_duration Nat
            (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 0 (instOfNatNat 0))
            (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0)))
```
