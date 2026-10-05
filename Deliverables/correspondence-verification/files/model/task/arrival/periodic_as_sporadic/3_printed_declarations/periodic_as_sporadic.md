# `periodic_as_sporadic`

- Kind (Rocq): Instance
- Rocq: `prosa.model.task.arrival.periodic_as_sporadic.periodic_as_sporadic`
- Lean: `Prosa.Model.Task.Arrival.PeriodicAsSporadic.periodic_as_sporadic`
- Certificate: `periodic_as_sporadic_correspondence`

## Official Rocq

```coq
periodic_as_sporadic : forall {Task : TaskType}, PeriodicModel Task -> SporadicModel Task

periodic_as_sporadic is not universe polymorphic
Arguments periodic_as_sporadic {Task H} _
periodic_as_sporadic is transparent
Expands to: Constant prosa.model.task.arrival.periodic_as_sporadic.periodic_as_sporadic
Declared in library prosa.model.task.arrival.periodic_as_sporadic, line 24, characters 2-124
@periodic_as_sporadic
     : forall Task : TaskType, PeriodicModel Task -> SporadicModel Task
```

Body:

```coq
periodic_as_sporadic =
fun Task : TaskType => [eta @task_period Task]
     : forall {Task : TaskType}, PeriodicModel Task -> SporadicModel Task

Arguments periodic_as_sporadic {Task H} _
```

## Lean

```lean
@Prosa.Model.Task.Arrival.PeriodicAsSporadic.periodic_as_sporadic : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Arrival.Periodic.PeriodicModel Task] → Prosa.Model.Task.Arrival.Sporadic.SporadicModel Task
```

Body:

```lean
@[instance_reducible] def Prosa.Model.Task.Arrival.PeriodicAsSporadic.periodic_as_sporadic.{u_1} : {Task :
    Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Arrival.Periodic.PeriodicModel Task] → Prosa.Model.Task.Arrival.Sporadic.SporadicModel Task :=
fun {Task} [DecidableEq Task] [Prosa.Model.Task.Arrival.Periodic.PeriodicModel Task] =>
  { task_min_inter_arrival_time := Prosa.Model.Task.Arrival.Periodic.task_period }
```

## Lean, imported into Rocq

```coq
Prosa_Model_Task_Arrival_PeriodicAsSporadic_periodic_as_sporadic
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task),
       Prosa_Model_Task_Arrival_Periodic_PeriodicModel Task
         inst_3 ->
       Prosa_Model_Task_Arrival_Sporadic_SporadicModel Task
         inst_3
```

Body:

```coq
Prosa_Model_Task_Arrival_PeriodicAsSporadic_periodic_as_sporadic@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_3 : DecidableEq Task)
  (inst_6 : 
   Prosa_Model_Task_Arrival_Periodic_PeriodicModel Task
     inst_3) =>
Prosa_Model_Task_Arrival_Sporadic_SporadicModel_mk Task
  inst_3
  (Prosa_Model_Task_Arrival_Periodic_PeriodicModel_task_period Task
     inst_3
     inst_6)
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task),
       Prosa_Model_Task_Arrival_Periodic_PeriodicModel Task
         inst_3 ->
       Prosa_Model_Task_Arrival_Sporadic_SporadicModel Task
         inst_3

Arguments Prosa_Model_Task_Arrival_PeriodicAsSporadic_periodic_as_sporadic Task
  inst_3
  inst_6
```
