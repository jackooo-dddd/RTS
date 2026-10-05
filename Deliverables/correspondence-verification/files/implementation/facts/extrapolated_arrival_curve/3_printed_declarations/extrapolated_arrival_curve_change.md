# `extrapolated_arrival_curve_change`

- Kind (Rocq): Lemma
- Rocq: `prosa.implementation.facts.extrapolated_arrival_curve.extrapolated_arrival_curve_change`
- Lean: `Prosa.Implementation.Facts.ExtrapolatedArrivalCurve.extrapolated_arrival_curve_change`
- Certificate: `facts_extrapolated_arrival_curve_change_certificate`

## Official Rocq

```coq
extrapolated_arrival_curve_change :
forall ac_prefix : ArrivalCurvePrefix,
is_true (positive_horizon ac_prefix) ->
is_true (sorted_leq_steps ac_prefix) ->
forall t : duration,
is_true (extrapolated_arrival_curve ac_prefix t != extrapolated_arrival_curve ac_prefix (t + 1)) ->
is_true (t %/ horizon_of ac_prefix < (t + 1) %/ horizon_of ac_prefix) \/
t %/ horizon_of ac_prefix = (t + 1) %/ horizon_of ac_prefix /\
is_true
  (value_at ac_prefix (t %% horizon_of ac_prefix) < value_at ac_prefix ((t + 1) %% horizon_of ac_prefix))

extrapolated_arrival_curve_change is not universe polymorphic
Arguments extrapolated_arrival_curve_change ac_prefix H_positive H_sorted_leq t _
extrapolated_arrival_curve_change is opaque
Expands to: Constant prosa.implementation.facts.extrapolated_arrival_curve.extrapolated_arrival_curve_change
Declared in library prosa.implementation.facts.extrapolated_arrival_curve, line 242, characters 8-41
extrapolated_arrival_curve_change
     : forall ac_prefix : ArrivalCurvePrefix,
       is_true (positive_horizon ac_prefix) ->
       is_true (sorted_leq_steps ac_prefix) ->
       forall t : duration,
       is_true (extrapolated_arrival_curve ac_prefix t != extrapolated_arrival_curve ac_prefix (t + 1)) ->
       is_true (t %/ horizon_of ac_prefix < (t + 1) %/ horizon_of ac_prefix) \/
       t %/ horizon_of ac_prefix = (t + 1) %/ horizon_of ac_prefix /\
       is_true
         (value_at ac_prefix (t %% horizon_of ac_prefix) <
          value_at ac_prefix ((t + 1) %% horizon_of ac_prefix))
```

## Lean

```lean
Prosa.Implementation.Facts.ExtrapolatedArrivalCurve.extrapolated_arrival_curve_change : ∀
  (ac_prefix : Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.ArrivalCurvePrefix),
  Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.positive_horizon ac_prefix = true →
    Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.sorted_leq_steps ac_prefix = true →
      ∀ (t : ℕ),
        Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.extrapolated_arrival_curve ac_prefix t ≠
            Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.extrapolated_arrival_curve ac_prefix (t + 1) →
          t / Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.horizon_of ac_prefix <
              (t + 1) / Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.horizon_of ac_prefix ∨
            t / Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.horizon_of ac_prefix =
                (t + 1) / Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.horizon_of ac_prefix ∧
              Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.value_at ac_prefix
                  (t % Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.horizon_of ac_prefix) <
                Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.value_at ac_prefix
                  ((t + 1) % Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.horizon_of ac_prefix)
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Facts_ExtrapolatedArrivalCurve_extrapolated_arrival_curve_change
     : forall ac_prefix : Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_ArrivalCurvePrefix,
       @eq Bool (Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_positive_horizon ac_prefix)
         Bool_true ->
       @eq Bool (Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_sorted_leq_steps ac_prefix)
         Bool_true ->
       forall t : Nat,
       Ne Nat
         (Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_extrapolated_arrival_curve ac_prefix t)
         (Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_extrapolated_arrival_curve ac_prefix
            (HAdd_hAdd_inst7 Nat Prosa_Behavior_Time_duration Nat (instHAdd_inst1 Nat instAddNat) t
               (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 1 (instOfNatNat 1)))) ->
       Or
         (LT_lt_inst1 Nat instLTNat
            (HDiv_hDiv_inst7 Nat Prosa_Behavior_Time_duration Nat (instHDiv_inst1 Nat Nat_instDiv) t
               (Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_horizon_of ac_prefix))
            (HDiv_hDiv_inst7 Nat Prosa_Behavior_Time_duration Nat (instHDiv_inst1 Nat Nat_instDiv)
               (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat) t
                  (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1)))
               (Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_horizon_of ac_prefix)))
         (And
            (@eq Nat
               (HDiv_hDiv_inst7 Nat Prosa_Behavior_Time_duration Nat (instHDiv_inst1 Nat Nat_instDiv) t
                  (Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_horizon_of ac_prefix))
               (HDiv_hDiv_inst7 Nat Prosa_Behavior_Time_duration Nat (instHDiv_inst1 Nat Nat_instDiv)
                  (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat) t
                     (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1)))
                  (Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_horizon_of ac_prefix)))
            (LT_lt_inst1 Nat instLTNat
               (Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_value_at ac_prefix
                  (HMod_hMod_inst7 Nat Prosa_Behavior_Time_duration Nat (instHMod_inst1 Nat Nat_instMod) t
                     (Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_horizon_of ac_prefix)))
               (Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_value_at ac_prefix
                  (HMod_hMod_inst7 Nat Prosa_Behavior_Time_duration Nat (instHMod_inst1 Nat Nat_instMod)
                     (HAdd_hAdd_inst7 Nat Prosa_Behavior_Time_duration Nat (instHAdd_inst1 Nat instAddNat) t
                        (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 1 (instOfNatNat 1)))
                     (Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_horizon_of ac_prefix)))))
```
