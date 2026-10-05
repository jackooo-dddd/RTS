# `step_at_agrees_with_steps_of`

- Kind (Rocq): Lemma
- Rocq: `prosa.implementation.facts.extrapolated_arrival_curve.step_at_agrees_with_steps_of`
- Lean: `Prosa.Implementation.Facts.ExtrapolatedArrivalCurve.step_at_agrees_with_steps_of`
- Certificate: `facts_step_at_agrees_with_steps_of_certificate`

## Official Rocq

```coq
step_at_agrees_with_steps_of :
forall ac_prefix : ArrivalCurvePrefix,
is_true (sorted_ltn_steps ac_prefix) ->
forall t v : Equality.sort Datatypes_nat__canonical__eqtype_Equality,
is_true ((t, v) \in steps_of ac_prefix) -> step_at ac_prefix t = (t, v)

step_at_agrees_with_steps_of is not universe polymorphic
Arguments step_at_agrees_with_steps_of ac_prefix H_sorted_ltn t v _
step_at_agrees_with_steps_of is opaque
Expands to: Constant prosa.implementation.facts.extrapolated_arrival_curve.step_at_agrees_with_steps_of
Declared in library prosa.implementation.facts.extrapolated_arrival_curve, line 170, characters 8-36
step_at_agrees_with_steps_of
     : forall ac_prefix : ArrivalCurvePrefix,
       is_true (sorted_ltn_steps ac_prefix) ->
       forall t v : Equality.sort Datatypes_nat__canonical__eqtype_Equality,
       is_true ((t, v) \in steps_of ac_prefix) -> step_at ac_prefix t = (t, v)
```

## Lean

```lean
Prosa.Implementation.Facts.ExtrapolatedArrivalCurve.step_at_agrees_with_steps_of : ∀
  (ac_prefix : Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.ArrivalCurvePrefix),
  Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.sorted_ltn_steps ac_prefix = true →
    ∀ (t v : ℕ),
      (t, v) ∈ Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.steps_of ac_prefix →
        Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.step_at ac_prefix t = (t, v)
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Facts_ExtrapolatedArrivalCurve_step_at_agrees_with_steps_of
     : forall ac_prefix : Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_ArrivalCurvePrefix,
       @eq Bool (Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_sorted_ltn_steps ac_prefix)
         Bool_true ->
       forall t v : Nat,
       Membership_mem_inst3 (Prod_inst3 Nat Nat) (List_inst1 (Prod_inst3 Prosa_Behavior_Time_duration Nat))
         (List_instMembership_inst1 (Prod_inst3 Prosa_Behavior_Time_duration Nat))
         (Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_steps_of ac_prefix)
         (Prod_mk_inst3 Nat Nat t v) ->
       @eq (Prod_inst3 Prosa_Behavior_Time_duration Nat)
         (Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_step_at ac_prefix t)
         (Prod_mk_inst3 Nat Nat t v)
```
