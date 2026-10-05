# `valid_request_bound_function`

- Kind (Rocq): Definition
- Rocq: `prosa.model.task.arrival.request_bound_functions.valid_request_bound_function`
- Lean: `Prosa.Model.Task.Arrival.RequestBoundFunctions.valid_request_bound_function`
- Certificate: `valid_request_bound_function_correspondence`

## Official Rocq

```coq
valid_request_bound_function : (duration -> work) -> Prop

valid_request_bound_function is not universe polymorphic
Arguments valid_request_bound_function request_bound%function_scope
valid_request_bound_function is transparent
Expands to: Constant prosa.model.task.arrival.request_bound_functions.valid_request_bound_function
Declared in library prosa.model.task.arrival.request_bound_functions, line 52, characters 13-41
valid_request_bound_function
     : (duration -> work) -> Prop
```

Body:

```coq
valid_request_bound_function =
fun request_bound : duration -> work => request_bound 0 = 0 /\ @monotone nat leq request_bound
     : (duration -> work) -> Prop

Arguments valid_request_bound_function request_bound%function_scope
```

## Lean

```lean
Prosa.Model.Task.Arrival.RequestBoundFunctions.valid_request_bound_function : (Prosa.Behavior.Time.duration →
    Prosa.Behavior.Job.work) →
  Prop
```

Body:

```lean
def Prosa.Model.Task.Arrival.RequestBoundFunctions.valid_request_bound_function : (Prosa.Behavior.Time.duration →
    Prosa.Behavior.Job.work) →
  Prop :=
fun request_bound => request_bound 0 = 0 ∧ Prosa.Util.Rel.monotone (fun x y => decide (x ≤ y)) request_bound
```

## Lean, imported into Rocq

```coq
Prosa_Model_Task_Arrival_RequestBoundFunctions_valid_request_bound_function
     : (Prosa_Behavior_Time_duration -> Prosa_Behavior_Job_work) -> SProp
```

Body:

```coq
Prosa_Model_Task_Arrival_RequestBoundFunctions_valid_request_bound_function@{} =
fun request_bound : Prosa_Behavior_Time_duration -> Prosa_Behavior_Job_work =>
And
  (@eq Prosa_Behavior_Job_work
     (request_bound (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 0 (instOfNatNat 0)))
     (OfNat_ofNat_inst1 Prosa_Behavior_Job_work 0 (instOfNatNat 0)))
  (Prosa_Util_Rel_monotone_inst1 Prosa_Behavior_Time_duration
     (fun x y : Prosa_Behavior_Time_duration =>
      Decidable_decide (LE_le_inst1 Prosa_Behavior_Time_duration instLENat x y) (Nat_decLe x y))
     request_bound)
     : (Prosa_Behavior_Time_duration -> Prosa_Behavior_Job_work) -> SProp

Arguments Prosa_Model_Task_Arrival_RequestBoundFunctions_valid_request_bound_function
  request_bound%_function_scope
```
