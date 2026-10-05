# `valid_arrivals`

- Kind (Rocq): Definition
- Rocq: `prosa.implementation.refinements.arrival_curve.valid_arrivals`
- Lean: `Prosa.Implementation.Refinements.ArrivalCurve.valid_arrivals`
- Certificate: `valid_arrivals_correspondence`

## Official Rocq

```coq
valid_arrivals : Equality.sort Task -> bool

valid_arrivals is not universe polymorphic
Arguments valid_arrivals tsk
valid_arrivals is transparent
Expands to: Constant prosa.implementation.refinements.arrival_curve.valid_arrivals
Declared in library prosa.implementation.refinements.arrival_curve, line 33, characters 11-25
valid_arrivals
     : Equality.sort Task -> bool
```

Body:

```coq
valid_arrivals =
fun tsk : Equality.sort Task =>
match task_arrival tsk with
| @Periodic p => 0 < p
| @Sporadic m => 0 < m
| @ArrivalPrefix emax_vec => valid_arrival_curve_prefix_dec emax_vec
end
     : Equality.sort Task -> bool

Arguments valid_arrivals tsk
```

## Lean

```lean
Prosa.Implementation.Refinements.ArrivalCurve.valid_arrivals : Prosa.Implementation.Refinements.Task.Task → Bool
```

Body:

```lean
def Prosa.Implementation.Refinements.ArrivalCurve.valid_arrivals : Prosa.Implementation.Refinements.Task.Task → Bool :=
fun tsk =>
  match tsk.task_arrival with
  | Prosa.Implementation.Definitions.ArrivalBound.task_arrivals_bound.Periodic p => decide (1 ≤ p)
  | Prosa.Implementation.Definitions.ArrivalBound.task_arrivals_bound.Sporadic m => decide (1 ≤ m)
  | Prosa.Implementation.Definitions.ArrivalBound.task_arrivals_bound.ArrivalPrefix emax_vec =>
    Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.valid_arrival_curve_prefix_dec emax_vec
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_ArrivalCurve_valid_arrivals
     : Prosa_Implementation_Refinements_Task_Task -> Bool
```

Body:

```coq
Prosa_Implementation_Refinements_ArrivalCurve_valid_arrivals@{} =
fun tsk : Prosa_Implementation_Refinements_Task_Task =>
Prosa_Implementation_Refinements_ArrivalCurve_valid_arrivals_match_1
  (fun _ : Prosa_Implementation_Definitions_ArrivalBound_task_arrivals_bound => Bool)
  (Prosa_Implementation_Definitions_Task_concrete_task_task_arrival tsk)
  (fun p : Nat =>
   Decidable_decide (LE_le_inst1 Nat instLENat (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1)) p)
     (Nat_decLe (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1)) p))
  (fun p : Nat =>
   Decidable_decide (LE_le_inst1 Nat instLENat (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1)) p)
     (Nat_decLe (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1)) p))
  (fun emax_vec : Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_ArrivalCurvePrefix =>
   Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_valid_arrival_curve_prefix_dec emax_vec)
     : Prosa_Implementation_Refinements_Task_Task -> Bool

Arguments Prosa_Implementation_Refinements_ArrivalCurve_valid_arrivals tsk
```
