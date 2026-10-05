# `hyperperiod_index`

- Kind (Rocq): Definition
- Rocq: `prosa.analysis.definitions.hyperperiod.hyperperiod_index`
- Lean: `Prosa.Analysis.Definitions.Hyperperiod.hyperperiod_index`
- Certificate: `hyperperiod_index_correspondence`

## Official Rocq

```coq
hyperperiod_index :
forall {Task : TaskType},
TaskOffset Task -> PeriodicModel Task -> TaskSet (Equality.sort Task) -> instant -> nat

hyperperiod_index is not universe polymorphic
Arguments hyperperiod_index {Task H H0} ts t
hyperperiod_index is transparent
Expands to: Constant prosa.analysis.definitions.hyperperiod.hyperperiod_index
Declared in library prosa.analysis.definitions.hyperperiod, line 50, characters 13-30
@hyperperiod_index
     : forall Task : TaskType,
       TaskOffset Task -> PeriodicModel Task -> TaskSet (Equality.sort Task) -> instant -> nat
```

Body:

```coq
hyperperiod_index =
fun (Task : TaskType) (H : TaskOffset Task) (H0 : PeriodicModel Task) (ts : TaskSet (Equality.sort Task)) =>
let O_max := @max_task_offset Task H ts in
let HP := @hyperperiod Task H0 ts in fun t : instant => (t - O_max) %/ HP
     : forall {Task : TaskType},
       TaskOffset Task -> PeriodicModel Task -> TaskSet (Equality.sort Task) -> instant -> nat

Arguments hyperperiod_index {Task H H0} ts t
```

## Lean

```lean
@Prosa.Analysis.Definitions.Hyperperiod.hyperperiod_index : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Offset.TaskOffset Task] →
      [Prosa.Model.Task.Arrival.Periodic.PeriodicModel Task] →
        Prosa.Model.Task.Concept.TaskSet Task → Prosa.Behavior.Time.instant → ℕ
```

Body:

```lean
def Prosa.Analysis.Definitions.Hyperperiod.hyperperiod_index.{u_1} : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Offset.TaskOffset Task] →
      [Prosa.Model.Task.Arrival.Periodic.PeriodicModel Task] →
        Prosa.Model.Task.Concept.TaskSet Task → Prosa.Behavior.Time.instant → ℕ :=
fun {Task} [DecidableEq Task] [Prosa.Model.Task.Offset.TaskOffset Task]
    [Prosa.Model.Task.Arrival.Periodic.PeriodicModel Task] ts t =>
  (t - Prosa.Model.Task.Offset.max_task_offset ts) / Prosa.Analysis.Definitions.Hyperperiod.hyperperiod ts
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Definitions_Hyperperiod_hyperperiod_index
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Task_Offset_TaskOffset Task
         inst_3 ->
       Prosa_Model_Task_Arrival_Periodic_PeriodicModel Task
         inst_3 ->
       Prosa_Model_Task_Concept_TaskSet Task -> Prosa_Behavior_Time_instant -> Nat
```

Body:

```coq
Prosa_Analysis_Definitions_Hyperperiod_hyperperiod_index@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_3 : DecidableEq Task)
  (inst_6 : 
   Prosa_Model_Task_Offset_TaskOffset Task
     inst_3)
  (inst_9 : 
   Prosa_Model_Task_Arrival_Periodic_PeriodicModel Task
     inst_3)
  (ts : Prosa_Model_Task_Concept_TaskSet Task) (t : Prosa_Behavior_Time_instant) =>
HDiv_hDiv_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_duration Prosa_Behavior_Time_instant
  (instHDiv_inst1 Prosa_Behavior_Time_instant Nat_instDiv)
  (HSub_hSub_inst7 Prosa_Behavior_Time_instant Nat Prosa_Behavior_Time_instant
     (instHSub_inst1 Prosa_Behavior_Time_instant instSubNat) t
     (Prosa_Model_Task_Offset_max_task_offset Task
        inst_3
        inst_6 ts))
  (Prosa_Analysis_Definitions_Hyperperiod_hyperperiod Task
     inst_3
     inst_9 ts)
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Task_Offset_TaskOffset Task
         inst_3 ->
       Prosa_Model_Task_Arrival_Periodic_PeriodicModel Task
         inst_3 ->
       Prosa_Model_Task_Concept_TaskSet Task -> Prosa_Behavior_Time_instant -> Nat

Arguments Prosa_Analysis_Definitions_Hyperperiod_hyperperiod_index Task
  inst_3
  inst_6
  inst_9 ts 
  t2
```
