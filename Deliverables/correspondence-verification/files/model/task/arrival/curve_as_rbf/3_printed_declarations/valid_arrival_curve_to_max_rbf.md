# `valid_arrival_curve_to_max_rbf`

- Kind (Rocq): Theorem
- Rocq: `prosa.model.task.arrival.curve_as_rbf.valid_arrival_curve_to_max_rbf`
- Lean: `Prosa.Model.Task.Arrival.CurveAsRbf.valid_arrival_curve_to_max_rbf`
- Certificate: `valid_arrival_curve_to_max_rbf_correspondence`

## Official Rocq

```coq
valid_arrival_curve_to_max_rbf :
forall {Task : TaskType} {H : TaskCost Task} (tsk : Equality.sort Task)
  (arrivals : Equality.sort Task -> duration -> nat),
valid_arrival_curve (arrivals tsk) -> valid_request_bound_function (@task_max_rbf Task H arrivals tsk)

valid_arrival_curve_to_max_rbf is not universe polymorphic
Arguments valid_arrival_curve_to_max_rbf {Task H} tsk arrivals%function_scope _
valid_arrival_curve_to_max_rbf is opaque
Expands to: Constant prosa.model.task.arrival.curve_as_rbf.valid_arrival_curve_to_max_rbf
Declared in library prosa.model.task.arrival.curve_as_rbf, line 49, characters 12-42
@valid_arrival_curve_to_max_rbf
     : forall (Task : TaskType) (H : TaskCost Task) (tsk : Equality.sort Task)
         (arrivals : Equality.sort Task -> duration -> nat),
       valid_arrival_curve (arrivals tsk) -> valid_request_bound_function (@task_max_rbf Task H arrivals tsk)
```

## Lean

```lean
@Prosa.Model.Task.Arrival.CurveAsRbf.valid_arrival_curve_to_max_rbf : ∀ {Task : Prosa.Model.Task.Concept.TaskType}
  [inst : DecidableEq Task] [inst_1 : Prosa.Model.Task.Concept.TaskCost Task] (tsk : Task)
  (arrivals : Task → Prosa.Behavior.Time.duration → ℕ),
  Prosa.Model.Task.Arrival.Curves.valid_arrival_curve (arrivals tsk) →
    Prosa.Model.Task.Arrival.RequestBoundFunctions.valid_request_bound_function
      (Prosa.Model.Task.Arrival.CurveAsRbf.task_max_rbf arrivals tsk)
```

## Lean, imported into Rocq

```coq
Prosa_Model_Task_Arrival_CurveAsRbf_valid_arrival_curve_to_max_rbf
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (inst_6 : 
          Prosa_Model_Task_Concept_TaskCost Task
            inst_3)
         (tsk : Task) (arrivals : Task -> Prosa_Behavior_Time_duration -> Nat),
       Prosa_Model_Task_Arrival_Curves_valid_arrival_curve (arrivals tsk) ->
       Prosa_Model_Task_Arrival_RequestBoundFunctions_valid_request_bound_function
         (Prosa_Model_Task_Arrival_CurveAsRbf_task_max_rbf Task
            inst_3
            inst_6 arrivals tsk)
```
