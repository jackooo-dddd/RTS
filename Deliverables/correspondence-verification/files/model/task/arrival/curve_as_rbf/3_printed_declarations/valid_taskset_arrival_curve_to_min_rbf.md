# `valid_taskset_arrival_curve_to_min_rbf`

- Kind (Rocq): Corollary
- Rocq: `prosa.model.task.arrival.curve_as_rbf.valid_taskset_arrival_curve_to_min_rbf`
- Lean: `Prosa.Model.Task.Arrival.CurveAsRbf.valid_taskset_arrival_curve_to_min_rbf`
- Certificate: `valid_taskset_arrival_curve_to_min_rbf_correspondence`

## Official Rocq

```coq
valid_taskset_arrival_curve_to_min_rbf :
forall {Task : TaskType} {H0 : TaskMinCost Task} {MinArr : MinArrivals Task}
  (ts : TaskSet (Equality.sort Task)),
@valid_taskset_arrival_curve Task ts MinArr ->
@valid_taskset_request_bound_function Task ts (@MinArrivalsRBF Task H0 MinArr)

valid_taskset_arrival_curve_to_min_rbf is not universe polymorphic
Arguments valid_taskset_arrival_curve_to_min_rbf {Task H0 MinArr} ts _ tsk _
valid_taskset_arrival_curve_to_min_rbf is opaque
Expands to: Constant prosa.model.task.arrival.curve_as_rbf.valid_taskset_arrival_curve_to_min_rbf
Declared in library prosa.model.task.arrival.curve_as_rbf, line 138, characters 14-52
@valid_taskset_arrival_curve_to_min_rbf
     : forall (Task : TaskType) (H0 : TaskMinCost Task) (MinArr : MinArrivals Task)
         (ts : TaskSet (Equality.sort Task)),
       @valid_taskset_arrival_curve Task ts MinArr ->
       @valid_taskset_request_bound_function Task ts (@MinArrivalsRBF Task H0 MinArr)
```

## Lean

```lean
@Prosa.Model.Task.Arrival.CurveAsRbf.valid_taskset_arrival_curve_to_min_rbf : ∀
  {Task : Prosa.Model.Task.Concept.TaskType} [inst : DecidableEq Task]
  [inst_1 : Prosa.Model.Task.Concept.TaskMinCost Task] [MinArr : Prosa.Model.Task.Arrival.Curves.MinArrivals Task]
  (ts : Prosa.Model.Task.Concept.TaskSet Task),
  Prosa.Model.Task.Arrival.Curves.valid_taskset_arrival_curve ts Prosa.Model.Task.Arrival.Curves.min_arrivals →
    Prosa.Model.Task.Arrival.RequestBoundFunctions.valid_taskset_request_bound_function ts
      Prosa.Model.Task.Arrival.RequestBoundFunctions.min_request_bound
```

## Lean, imported into Rocq

```coq
Prosa_Model_Task_Arrival_CurveAsRbf_valid_taskset_arrival_curve_to_min_rbf
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (inst_6 : 
          Prosa_Model_Task_Concept_TaskMinCost Task
            inst_3)
         (MinArr : Prosa_Model_Task_Arrival_Curves_MinArrivals Task
                     inst_3)
         (ts : Prosa_Model_Task_Concept_TaskSet Task),
       Prosa_Model_Task_Arrival_Curves_valid_taskset_arrival_curve Task
         inst_3 ts
         (Prosa_Model_Task_Arrival_Curves_MinArrivals_min_arrivals Task
            inst_3 MinArr) ->
       Prosa_Model_Task_Arrival_RequestBoundFunctions_valid_taskset_request_bound_function Task
         inst_3 ts
         (Prosa_Model_Task_Arrival_RequestBoundFunctions_MinRequestBound_min_request_bound Task
            inst_3
            (Prosa_Model_Task_Arrival_CurveAsRbf_MinArrivalsRBF Task
               inst_3
               inst_6 MinArr))
```
