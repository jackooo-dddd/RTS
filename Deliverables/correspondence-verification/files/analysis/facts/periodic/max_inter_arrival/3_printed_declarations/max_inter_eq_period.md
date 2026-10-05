# `max_inter_eq_period`

- Kind (Rocq): Instance
- Rocq: `prosa.analysis.facts.periodic.max_inter_arrival.max_inter_eq_period`
- Lean: `Prosa.Analysis.Facts.Periodic.MaxInterArrival.max_inter_eq_period`
- Certificate: `max_inter_eq_period_correspondence`

## Official Rocq

```coq
max_inter_eq_period : forall {Task : TaskType}, PeriodicModel Task -> TaskMaxInterArrival Task

max_inter_eq_period is not universe polymorphic
Arguments max_inter_eq_period {Task H} _
max_inter_eq_period is transparent
Expands to: Constant prosa.analysis.facts.periodic.max_inter_arrival.max_inter_eq_period
Declared in library prosa.analysis.facts.periodic.max_inter_arrival, line 21, characters 2-129
@max_inter_eq_period
     : forall Task : TaskType, PeriodicModel Task -> TaskMaxInterArrival Task
```

Body:

```coq
max_inter_eq_period =
fun Task : TaskType => [eta @task_period Task]
     : forall {Task : TaskType}, PeriodicModel Task -> TaskMaxInterArrival Task

Arguments max_inter_eq_period {Task H} _
```

## Lean

```lean
@Prosa.Analysis.Facts.Periodic.MaxInterArrival.max_inter_eq_period : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Arrival.Periodic.PeriodicModel Task] →
      Prosa.Model.Task.Arrival.Task_max_inter_arrival.TaskMaxInterArrival Task
```

Body:

```lean
@[instance_reducible] def Prosa.Analysis.Facts.Periodic.MaxInterArrival.max_inter_eq_period.{u_1} : {Task :
    Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Arrival.Periodic.PeriodicModel Task] →
      Prosa.Model.Task.Arrival.Task_max_inter_arrival.TaskMaxInterArrival Task :=
fun {Task} [DecidableEq Task] [Prosa.Model.Task.Arrival.Periodic.PeriodicModel Task] =>
  { task_max_inter_arrival_time := Prosa.Model.Task.Arrival.Periodic.task_period }
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Periodic_MaxInterArrival_max_inter_eq_period
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task),
       Prosa_Model_Task_Arrival_Periodic_PeriodicModel Task
         inst_3 ->
       Prosa_Model_Task_Arrival_Task_max_inter_arrival_TaskMaxInterArrival Task
         inst_3
```

Body:

```coq
Prosa_Analysis_Facts_Periodic_MaxInterArrival_max_inter_eq_period@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_3 : DecidableEq Task)
  (inst_6 : 
   Prosa_Model_Task_Arrival_Periodic_PeriodicModel Task
     inst_3) =>
Prosa_Model_Task_Arrival_Task_max_inter_arrival_TaskMaxInterArrival_mk Task
  inst_3
  (Prosa_Model_Task_Arrival_Periodic_PeriodicModel_task_period Task
     inst_3
     inst_6)
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task),
       Prosa_Model_Task_Arrival_Periodic_PeriodicModel Task
         inst_3 ->
       Prosa_Model_Task_Arrival_Task_max_inter_arrival_TaskMaxInterArrival Task
         inst_3

Arguments Prosa_Analysis_Facts_Periodic_MaxInterArrival_max_inter_eq_period Task
  inst_3
  inst_6
```
