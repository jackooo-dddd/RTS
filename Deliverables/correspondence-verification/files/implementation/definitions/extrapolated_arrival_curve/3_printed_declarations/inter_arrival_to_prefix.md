# `inter_arrival_to_prefix`

- Kind (Rocq): Definition
- Rocq: `prosa.implementation.definitions.extrapolated_arrival_curve.inter_arrival_to_prefix`
- Lean: `Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.inter_arrival_to_prefix`
- Certificate: `eac_inter_arrival_to_prefix_correspondence`

## Official Rocq

```coq
inter_arrival_to_prefix : nat -> ArrivalCurvePrefix

inter_arrival_to_prefix is not universe polymorphic
Arguments inter_arrival_to_prefix p%nat_scope
inter_arrival_to_prefix is transparent
Expands to: Constant prosa.implementation.definitions.extrapolated_arrival_curve.inter_arrival_to_prefix
Declared in library prosa.implementation.definitions.extrapolated_arrival_curve, line 35, characters 11-34
inter_arrival_to_prefix
     : nat -> ArrivalCurvePrefix
```

Body:

```coq
inter_arrival_to_prefix = (@pair nat (seq (nat * nat)))^~ [:: (1, 1)]
     : nat -> ArrivalCurvePrefix

Arguments inter_arrival_to_prefix p%nat_scope
```

## Lean

```lean
Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.inter_arrival_to_prefix : ℕ →
  Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.ArrivalCurvePrefix
```

Body:

```lean
def Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.inter_arrival_to_prefix : ℕ →
  Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.ArrivalCurvePrefix :=
fun p => (p, [(1, 1)])
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_inter_arrival_to_prefix
     : Nat -> Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_ArrivalCurvePrefix
```

Body:

```coq
Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_inter_arrival_to_prefix@{} =
fun p : Nat =>
Prod_mk_inst3 Prosa_Behavior_Time_duration (List_inst1 (Prod_inst3 Prosa_Behavior_Time_duration Nat)) p
  (List_cons_inst1 (Prod_inst3 Prosa_Behavior_Time_duration Nat)
     (Prod_mk_inst3 Prosa_Behavior_Time_duration Nat
        (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 1 (instOfNatNat 1))
        (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1)))
     (List_nil_inst1 (Prod_inst3 Prosa_Behavior_Time_duration Nat)))
     : Nat -> Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_ArrivalCurvePrefix

Arguments Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_inter_arrival_to_prefix p%_Nat_scope
```
