# `hyperperiod`

- Kind (Rocq): Definition
- Rocq: `prosa.analysis.definitions.hyperperiod.hyperperiod`
- Lean: `Prosa.Analysis.Definitions.Hyperperiod.hyperperiod`
- Certificate: `hyperperiod_correspondence`

## Official Rocq

```coq
hyperperiod : forall {Task : TaskType}, PeriodicModel Task -> TaskSet (Equality.sort Task) -> duration

hyperperiod is not universe polymorphic
Arguments hyperperiod {Task H} ts
hyperperiod is transparent
Expands to: Constant prosa.analysis.definitions.hyperperiod.hyperperiod
Declared in library prosa.analysis.definitions.hyperperiod, line 15, characters 13-24
@hyperperiod
     : forall Task : TaskType, PeriodicModel Task -> TaskSet (Equality.sort Task) -> duration
```

Body:

```coq
hyperperiod =
fun (Task : TaskType) (H : PeriodicModel Task) (ts : TaskSet (Equality.sort Task)) =>
lcml [seq @task_period Task H i | i <- ts]
     : forall {Task : TaskType}, PeriodicModel Task -> TaskSet (Equality.sort Task) -> duration

Arguments hyperperiod {Task H} ts
```

## Lean

```lean
@Prosa.Analysis.Definitions.Hyperperiod.hyperperiod : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Arrival.Periodic.PeriodicModel Task] →
      Prosa.Model.Task.Concept.TaskSet Task → Prosa.Behavior.Time.duration
```

Body:

```lean
def Prosa.Analysis.Definitions.Hyperperiod.hyperperiod.{u_1} : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Arrival.Periodic.PeriodicModel Task] →
      Prosa.Model.Task.Concept.TaskSet Task → Prosa.Behavior.Time.duration :=
fun {Task} [DecidableEq Task] [Prosa.Model.Task.Arrival.Periodic.PeriodicModel Task] ts =>
  Prosa.Util.Lcmseq.lcml (List.map Prosa.Model.Task.Arrival.Periodic.task_period ts)
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Definitions_Hyperperiod_hyperperiod
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Task_Arrival_Periodic_PeriodicModel Task
         inst_3 ->
       Prosa_Model_Task_Concept_TaskSet Task -> Prosa_Behavior_Time_duration
```

Body:

```coq
Prosa_Analysis_Definitions_Hyperperiod_hyperperiod@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_3 : DecidableEq Task)
  (inst_6 : 
   Prosa_Model_Task_Arrival_Periodic_PeriodicModel Task
     inst_3)
  (ts : Prosa_Model_Task_Concept_TaskSet Task) =>
Prosa_Util_Lcmseq_lcml
  (List_map_inst2 Task Nat
     (Prosa_Model_Task_Arrival_Periodic_PeriodicModel_task_period Task
        inst_3
        inst_6)
     ts)
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Task_Arrival_Periodic_PeriodicModel Task
         inst_3 ->
       Prosa_Model_Task_Concept_TaskSet Task -> Prosa_Behavior_Time_duration

Arguments Prosa_Analysis_Definitions_Hyperperiod_hyperperiod Task
  inst_3
  inst_6 ts
```
