# `valid_taskset_arrival_curve_to_max_rbf`

- Kind (Rocq): Corollary
- Rocq: `prosa.model.task.arrival.curve_as_rbf.valid_taskset_arrival_curve_to_max_rbf`
- Lean: `Prosa.Model.Task.Arrival.CurveAsRbf.valid_taskset_arrival_curve_to_max_rbf`
- Certificate: `valid_taskset_arrival_curve_to_max_rbf_correspondence`

## Official Rocq

```coq
valid_taskset_arrival_curve_to_max_rbf :
forall {Task : TaskType} {H : TaskCost Task} {MaxArr : MaxArrivals Task} (ts : TaskSet (Equality.sort Task)),
@valid_taskset_arrival_curve Task ts MaxArr ->
@valid_taskset_request_bound_function Task ts (@MaxArrivalsRBF Task H MaxArr)

valid_taskset_arrival_curve_to_max_rbf is not universe polymorphic
Arguments valid_taskset_arrival_curve_to_max_rbf {Task H MaxArr} ts _ tsk _
valid_taskset_arrival_curve_to_max_rbf is opaque
Expands to: Constant prosa.model.task.arrival.curve_as_rbf.valid_taskset_arrival_curve_to_max_rbf
Declared in library prosa.model.task.arrival.curve_as_rbf, line 128, characters 14-52
@valid_taskset_arrival_curve_to_max_rbf
     : forall (Task : TaskType) (H : TaskCost Task) (MaxArr : MaxArrivals Task)
         (ts : TaskSet (Equality.sort Task)),
       @valid_taskset_arrival_curve Task ts MaxArr ->
       @valid_taskset_request_bound_function Task ts (@MaxArrivalsRBF Task H MaxArr)
```

## Lean

```lean
@Prosa.Model.Task.Arrival.CurveAsRbf.valid_taskset_arrival_curve_to_max_rbf : ∀
  {Task : Prosa.Model.Task.Concept.TaskType} [inst : DecidableEq Task] [inst_1 : Prosa.Model.Task.Concept.TaskCost Task]
  [MaxArr : Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] (ts : Prosa.Model.Task.Concept.TaskSet Task),
  Prosa.Model.Task.Arrival.Curves.valid_taskset_arrival_curve ts Prosa.Model.Task.Arrival.Curves.max_arrivals →
    Prosa.Model.Task.Arrival.RequestBoundFunctions.valid_taskset_request_bound_function ts
      Prosa.Model.Task.Arrival.RequestBoundFunctions.max_request_bound
```

## Lean, imported into Rocq

```coq
Prosa_Model_Task_Arrival_CurveAsRbf_valid_taskset_arrival_curve_to_max_rbf
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (inst_6 : 
          Prosa_Model_Task_Concept_TaskCost Task
            inst_3)
         (MaxArr : Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
                     inst_3)
         (ts : Prosa_Model_Task_Concept_TaskSet Task),
       Prosa_Model_Task_Arrival_Curves_valid_taskset_arrival_curve Task
         inst_3 ts
         (Prosa_Model_Task_Arrival_Curves_MaxArrivals_max_arrivals Task
            inst_3 MaxArr) ->
       Prosa_Model_Task_Arrival_RequestBoundFunctions_valid_taskset_request_bound_function Task
         inst_3 ts
         (Prosa_Model_Task_Arrival_RequestBoundFunctions_MaxRequestBound_max_request_bound Task
            inst_3
            (Prosa_Model_Task_Arrival_CurveAsRbf_MaxArrivalsRBF Task
               inst_3
               inst_6 MaxArr))
```
