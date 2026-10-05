# `value_at_change_is_in_steps_of`

- Kind (Rocq): Lemma
- Rocq: `prosa.implementation.facts.extrapolated_arrival_curve.value_at_change_is_in_steps_of`
- Lean: `Prosa.Implementation.Facts.ExtrapolatedArrivalCurve.value_at_change_is_in_steps_of`
- Certificate: `facts_value_at_change_is_in_steps_of_certificate`

## Official Rocq

```coq
value_at_change_is_in_steps_of :
forall ac_prefix : ArrivalCurvePrefix,
is_true (sorted_leq_steps ac_prefix) ->
is_true (no_inf_arrivals ac_prefix) ->
forall t : duration,
is_true (value_at ac_prefix t < value_at ac_prefix (t + 1)) ->
exists v : Equality.sort Datatypes_nat__canonical__eqtype_Equality,
  is_true ((t + 1, v) \in steps_of ac_prefix)

value_at_change_is_in_steps_of is not universe polymorphic
Arguments value_at_change_is_in_steps_of ac_prefix H_sorted_leq H_no_inf_arrivals t _
value_at_change_is_in_steps_of is opaque
Expands to: Constant prosa.implementation.facts.extrapolated_arrival_curve.value_at_change_is_in_steps_of
Declared in library prosa.implementation.facts.extrapolated_arrival_curve, line 86, characters 8-38
value_at_change_is_in_steps_of
     : forall ac_prefix : ArrivalCurvePrefix,
       is_true (sorted_leq_steps ac_prefix) ->
       is_true (no_inf_arrivals ac_prefix) ->
       forall t : duration,
       is_true (value_at ac_prefix t < value_at ac_prefix (t + 1)) ->
       exists v : Equality.sort Datatypes_nat__canonical__eqtype_Equality,
         is_true ((t + 1, v) \in steps_of ac_prefix)
```

## Lean

```lean
Prosa.Implementation.Facts.ExtrapolatedArrivalCurve.value_at_change_is_in_steps_of : ∀
  (ac_prefix : Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.ArrivalCurvePrefix),
  Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.sorted_leq_steps ac_prefix = true →
    Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.no_inf_arrivals ac_prefix = true →
      ∀ (t : ℕ),
        Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.value_at ac_prefix t <
            Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.value_at ac_prefix (t + 1) →
          ∃ v, (t + 1, v) ∈ Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.steps_of ac_prefix
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Facts_ExtrapolatedArrivalCurve_value_at_change_is_in_steps_of
     : forall ac_prefix : Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_ArrivalCurvePrefix,
       @eq Bool (Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_sorted_leq_steps ac_prefix)
         Bool_true ->
       @eq Bool (Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_no_inf_arrivals ac_prefix)
         Bool_true ->
       forall t : Nat,
       LT_lt_inst1 Nat instLTNat
         (Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_value_at ac_prefix t)
         (Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_value_at ac_prefix
            (HAdd_hAdd_inst7 Nat Prosa_Behavior_Time_duration Nat (instHAdd_inst1 Nat instAddNat) t
               (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 1 (instOfNatNat 1)))) ->
       Exists Nat
         (fun v : Nat =>
          Membership_mem_inst3 (Prod_inst3 Nat Nat)
            (List_inst1 (Prod_inst3 Prosa_Behavior_Time_duration Nat))
            (List_instMembership_inst1 (Prod_inst3 Prosa_Behavior_Time_duration Nat))
            (Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_steps_of ac_prefix)
            (Prod_mk_inst3 Nat Nat
               (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat) t
                  (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1)))
               v))
```
