# `MaxArrivalsRBF`

- Kind (Rocq): Instance
- Rocq: `prosa.model.task.arrival.curve_as_rbf.MaxArrivalsRBF`
- Lean: `Prosa.Model.Task.Arrival.CurveAsRbf.MaxArrivalsRBF`
- Certificate: `MaxArrivalsRBF_correspondence`

## Official Rocq

```coq
MaxArrivalsRBF : forall {Task : TaskType}, TaskCost Task -> MaxArrivals Task -> MaxRequestBound Task

MaxArrivalsRBF is not universe polymorphic
Arguments MaxArrivalsRBF {Task H MaxArr} _ _
MaxArrivalsRBF is transparent
Expands to: Constant prosa.model.task.arrival.curve_as_rbf.MaxArrivalsRBF
Declared in library prosa.model.task.arrival.curve_as_rbf, line 31, characters 2-93
@MaxArrivalsRBF
     : forall Task : TaskType, TaskCost Task -> MaxArrivals Task -> MaxRequestBound Task
```

Body:

```coq
MaxArrivalsRBF =
fun (Task : TaskType) (H : TaskCost Task) (MaxArr : MaxArrivals Task) =>
@task_max_rbf Task H (@max_arrivals Task MaxArr)
     : forall {Task : TaskType}, TaskCost Task -> MaxArrivals Task -> MaxRequestBound Task

Arguments MaxArrivalsRBF {Task H MaxArr} _ _
```

## Lean

```lean
@Prosa.Model.Task.Arrival.CurveAsRbf.MaxArrivalsRBF : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Concept.TaskCost Task] →
      [Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] →
        Prosa.Model.Task.Arrival.RequestBoundFunctions.MaxRequestBound Task
@[instance_reducible] def Prosa.Model.Task.Arrival.CurveAsRbf.MaxArrivalsRBF.{u_1} : {Task :
    Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Concept.TaskCost Task] →
      [Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] →
        Prosa.Model.Task.Arrival.RequestBoundFunctions.MaxRequestBound Task :=
fun {Task} [DecidableEq Task] [Prosa.Model.Task.Concept.TaskCost Task]
    [Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] =>
  { max_request_bound := Prosa.Model.Task.Arrival.CurveAsRbf.task_max_rbf Prosa.Model.Task.Arrival.Curves.max_arrivals }
```

## Lean, imported into Rocq

```coq
Prosa_Model_Task_Arrival_CurveAsRbf_MaxArrivalsRBF
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Task_Concept_TaskCost Task
         inst_3 ->
       Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
         inst_3 ->
       Prosa_Model_Task_Arrival_RequestBoundFunctions_MaxRequestBound Task
         inst_3
```

Body:

```coq
Prosa_Model_Task_Arrival_CurveAsRbf_MaxArrivalsRBF@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_3 : DecidableEq Task)
  (inst_6 : Prosa_Model_Task_Concept_TaskCost
                                                                                Task
                                                                                inst_3)
  (inst_9 : Prosa_Model_Task_Arrival_Curves_MaxArrivals
                                                                                Task
                                                                                inst_3) =>
Prosa_Model_Task_Arrival_RequestBoundFunctions_MaxRequestBound_mk Task
  inst_3
  (Prosa_Model_Task_Arrival_CurveAsRbf_task_max_rbf Task
     inst_3
     inst_6
     (Prosa_Model_Task_Arrival_Curves_MaxArrivals_max_arrivals Task
        inst_3
        inst_9))
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Task_Concept_TaskCost Task
         inst_3 ->
       Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
         inst_3 ->
       Prosa_Model_Task_Arrival_RequestBoundFunctions_MaxRequestBound Task
         inst_3

Arguments Prosa_Model_Task_Arrival_CurveAsRbf_MaxArrivalsRBF Task
  inst_3
  inst_6
  inst_9
```
