# `value_at_monotone`

- Kind (Rocq): Lemma
- Rocq: `prosa.implementation.facts.extrapolated_arrival_curve.value_at_monotone`
- Lean: `Prosa.Implementation.Facts.ExtrapolatedArrivalCurve.value_at_monotone`
- Certificate: `facts_value_at_monotone_certificate`

## Official Rocq

```coq
value_at_monotone :
forall ac_prefix : ArrivalCurvePrefix,
is_true (sorted_leq_steps ac_prefix) -> @monotone nat leq (value_at ac_prefix)

value_at_monotone is not universe polymorphic
Arguments value_at_monotone ac_prefix H_sorted_leq x y _
value_at_monotone is opaque
Expands to: Constant prosa.implementation.facts.extrapolated_arrival_curve.value_at_monotone
Declared in library prosa.implementation.facts.extrapolated_arrival_curve, line 48, characters 8-25
value_at_monotone
     : forall ac_prefix : ArrivalCurvePrefix,
       is_true (sorted_leq_steps ac_prefix) -> @monotone nat leq (value_at ac_prefix)
```

## Lean

```lean
Prosa.Implementation.Facts.ExtrapolatedArrivalCurve.value_at_monotone : ∀
  (ac_prefix : Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.ArrivalCurvePrefix),
  Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.sorted_leq_steps ac_prefix = true →
    ∀ (t1 t2 : ℕ),
      t1 ≤ t2 →
        Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.value_at ac_prefix t1 ≤
          Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.value_at ac_prefix t2
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Facts_ExtrapolatedArrivalCurve_value_at_monotone
     : forall ac_prefix : Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_ArrivalCurvePrefix,
       @eq Bool (Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_sorted_leq_steps ac_prefix)
         Bool_true ->
       forall t1 t2 : Nat,
       LE_le_inst1 Nat instLENat t1 t2 ->
       LE_le_inst1 Nat instLENat
         (Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_value_at ac_prefix t1)
         (Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_value_at ac_prefix t2)
```
