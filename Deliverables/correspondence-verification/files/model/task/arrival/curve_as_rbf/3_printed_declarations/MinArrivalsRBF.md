# `MinArrivalsRBF`

- Kind (Rocq): Instance
- Rocq: `prosa.model.task.arrival.curve_as_rbf.MinArrivalsRBF`
- Lean: `Prosa.Model.Task.Arrival.CurveAsRbf.MinArrivalsRBF`
- Certificate: `MinArrivalsRBF_correspondence`

## Official Rocq

```coq
MinArrivalsRBF : forall {Task : TaskType}, TaskMinCost Task -> MinArrivals Task -> MinRequestBound Task

MinArrivalsRBF is not universe polymorphic
Arguments MinArrivalsRBF {Task H0 MinArr} _ _
MinArrivalsRBF is transparent
Expands to: Constant prosa.model.task.arrival.curve_as_rbf.MinArrivalsRBF
Declared in library prosa.model.task.arrival.curve_as_rbf, line 32, characters 2-93
@MinArrivalsRBF
     : forall Task : TaskType, TaskMinCost Task -> MinArrivals Task -> MinRequestBound Task
```

Body:

```coq
MinArrivalsRBF =
fun (Task : TaskType) (H0 : TaskMinCost Task) (MinArr : MinArrivals Task) =>
@task_min_rbf Task H0 (@min_arrivals Task MinArr)
     : forall {Task : TaskType}, TaskMinCost Task -> MinArrivals Task -> MinRequestBound Task

Arguments MinArrivalsRBF {Task H0 MinArr} _ _
```

## Lean

```lean
@Prosa.Model.Task.Arrival.CurveAsRbf.MinArrivalsRBF : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Concept.TaskMinCost Task] →
      [Prosa.Model.Task.Arrival.Curves.MinArrivals Task] →
        Prosa.Model.Task.Arrival.RequestBoundFunctions.MinRequestBound Task
@[instance_reducible] def Prosa.Model.Task.Arrival.CurveAsRbf.MinArrivalsRBF.{u_1} : {Task :
    Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Concept.TaskMinCost Task] →
      [Prosa.Model.Task.Arrival.Curves.MinArrivals Task] →
        Prosa.Model.Task.Arrival.RequestBoundFunctions.MinRequestBound Task :=
fun {Task} [DecidableEq Task] [Prosa.Model.Task.Concept.TaskMinCost Task]
    [Prosa.Model.Task.Arrival.Curves.MinArrivals Task] =>
  { min_request_bound := Prosa.Model.Task.Arrival.CurveAsRbf.task_min_rbf Prosa.Model.Task.Arrival.Curves.min_arrivals }
```

## Lean, imported into Rocq

```coq
Prosa_Model_Task_Arrival_CurveAsRbf_MinArrivalsRBF
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Task_Concept_TaskMinCost Task
         inst_3 ->
       Prosa_Model_Task_Arrival_Curves_MinArrivals Task
         inst_3 ->
       Prosa_Model_Task_Arrival_RequestBoundFunctions_MinRequestBound Task
         inst_3
```

Body:

```coq
Prosa_Model_Task_Arrival_CurveAsRbf_MinArrivalsRBF@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_3 : DecidableEq Task)
  (inst_6 : Prosa_Model_Task_Concept_TaskMinCost
                                                                                Task
                                                                                inst_3)
  (inst_9 : Prosa_Model_Task_Arrival_Curves_MinArrivals
                                                                                Task
                                                                                inst_3) =>
Prosa_Model_Task_Arrival_RequestBoundFunctions_MinRequestBound_mk Task
  inst_3
  (Prosa_Model_Task_Arrival_CurveAsRbf_task_min_rbf Task
     inst_3
     inst_6
     (Prosa_Model_Task_Arrival_Curves_MinArrivals_min_arrivals Task
        inst_3
        inst_9))
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Task_Concept_TaskMinCost Task
         inst_3 ->
       Prosa_Model_Task_Arrival_Curves_MinArrivals Task
         inst_3 ->
       Prosa_Model_Task_Arrival_RequestBoundFunctions_MinRequestBound Task
         inst_3

Arguments Prosa_Model_Task_Arrival_CurveAsRbf_MinArrivalsRBF Task
  inst_3
  inst_6
  inst_9
```
