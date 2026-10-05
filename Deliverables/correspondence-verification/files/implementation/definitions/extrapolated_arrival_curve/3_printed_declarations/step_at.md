# `step_at`

- Kind (Rocq): Definition
- Rocq: `prosa.implementation.definitions.extrapolated_arrival_curve.step_at`
- Lean: `Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.step_at`
- Certificate: `eac_step_at_correspondence`

## Official Rocq

```coq
step_at : ArrivalCurvePrefix -> duration -> nat * nat

step_at is not universe polymorphic
Arguments step_at ac_prefix t
step_at is transparent
Expands to: Constant prosa.implementation.definitions.extrapolated_arrival_curve.step_at
Declared in library prosa.implementation.definitions.extrapolated_arrival_curve, line 51, characters 11-18
step_at
     : ArrivalCurvePrefix -> duration -> nat * nat
```

Body:

```coq
step_at =
fun (ac_prefix : ArrivalCurvePrefix) (t : duration) =>
@last (nat * nat) (0, 0) [seq step <- steps_of ac_prefix | step.1 <= t]
     : ArrivalCurvePrefix -> duration -> nat * nat

Arguments step_at ac_prefix t
```

## Lean

```lean
Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.step_at : Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.ArrivalCurvePrefix →
  Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration × ℕ
```

Body:

```lean
def Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.step_at : Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.ArrivalCurvePrefix →
  Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration × ℕ :=
fun ac_prefix t =>
  (List.filter (fun step => decide (step.1 ≤ t))
        (Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.steps_of ac_prefix)).getLastD
    (0, 0)
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_step_at
     : Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_ArrivalCurvePrefix ->
       Prosa_Behavior_Time_duration -> Prod_inst3 Prosa_Behavior_Time_duration Nat
```

Body:

```coq
Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_step_at@{} =
fun (ac_prefix : Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_ArrivalCurvePrefix)
  (t : Prosa_Behavior_Time_duration) =>
List_getLastD_inst1 (Prod_inst3 Prosa_Behavior_Time_duration Nat)
  (List_filter_inst1 (Prod_inst3 Prosa_Behavior_Time_duration Nat)
     (fun step : Prod_inst3 Prosa_Behavior_Time_duration Nat =>
      Decidable_decide
        (LE_le_inst1 Prosa_Behavior_Time_duration instLENat
           (Prod_fst_inst3 Prosa_Behavior_Time_duration Nat step) t)
        (Nat_decLe (Prod_fst_inst3 Prosa_Behavior_Time_duration Nat step) t))
     (Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_steps_of ac_prefix))
  (Prod_mk_inst3 Prosa_Behavior_Time_duration Nat
     (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 0 (instOfNatNat 0))
     (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0)))
     : Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_ArrivalCurvePrefix ->
       Prosa_Behavior_Time_duration -> Prod_inst3 Prosa_Behavior_Time_duration Nat

Arguments Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_step_at ac_prefix t
```
