# `valid_arrival_curve`

- Kind (Rocq): Definition
- Rocq: `prosa.model.task.arrival.curves.valid_arrival_curve`
- Lean: `Prosa.Model.Task.Arrival.Curves.valid_arrival_curve`
- Certificate: `valid_arrival_curve_correspondence`

## Official Rocq

```coq
valid_arrival_curve : (duration -> nat) -> Prop

valid_arrival_curve is not universe polymorphic
Arguments valid_arrival_curve num_arrivals%function_scope
valid_arrival_curve is transparent
Expands to: Constant prosa.model.task.arrival.curves.valid_arrival_curve
Declared in library prosa.model.task.arrival.curves, line 62, characters 13-32
valid_arrival_curve
     : (duration -> nat) -> Prop
```

Body:

```coq
valid_arrival_curve =
fun num_arrivals : duration -> nat => num_arrivals 0 = 0 /\ @monotone nat leq num_arrivals
     : (duration -> nat) -> Prop

Arguments valid_arrival_curve num_arrivals%function_scope
```

## Lean

```lean
Prosa.Model.Task.Arrival.Curves.valid_arrival_curve : (Prosa.Behavior.Time.duration → ℕ) → Prop
```

Body:

```lean
def Prosa.Model.Task.Arrival.Curves.valid_arrival_curve : (Prosa.Behavior.Time.duration → ℕ) → Prop :=
fun num_arrivals => num_arrivals 0 = 0 ∧ Prosa.Util.Rel.monotone (fun x y => decide (x ≤ y)) num_arrivals
```

## Lean, imported into Rocq

```coq
Prosa_Model_Task_Arrival_Curves_valid_arrival_curve
     : (Prosa_Behavior_Time_duration -> Nat) -> SProp
```

Body:

```coq
Prosa_Model_Task_Arrival_Curves_valid_arrival_curve@{} =
fun num_arrivals : Prosa_Behavior_Time_duration -> Nat =>
And
  (@eq Nat (num_arrivals (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 0 (instOfNatNat 0)))
     (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0)))
  (Prosa_Util_Rel_monotone_inst1 Prosa_Behavior_Time_duration
     (fun x y : Prosa_Behavior_Time_duration =>
      Decidable_decide (LE_le_inst1 Prosa_Behavior_Time_duration instLENat x y) (Nat_decLe x y))
     num_arrivals)
     : (Prosa_Behavior_Time_duration -> Nat) -> SProp

Arguments Prosa_Model_Task_Arrival_Curves_valid_arrival_curve num_arrivals%_function_scope
```
