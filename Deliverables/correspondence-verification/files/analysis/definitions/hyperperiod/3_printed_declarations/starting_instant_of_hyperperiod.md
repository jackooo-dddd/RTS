# `starting_instant_of_hyperperiod`

- Kind (Rocq): Definition
- Rocq: `prosa.analysis.definitions.hyperperiod.starting_instant_of_hyperperiod`
- Lean: `Prosa.Analysis.Definitions.Hyperperiod.starting_instant_of_hyperperiod`
- Certificate: `starting_instant_of_hyperperiod_correspondence`

## Official Rocq

```coq
starting_instant_of_hyperperiod :
forall {Task : TaskType},
TaskOffset Task -> PeriodicModel Task -> TaskSet (Equality.sort Task) -> instant -> nat

starting_instant_of_hyperperiod is not universe polymorphic
Arguments starting_instant_of_hyperperiod {Task H H0} ts t
starting_instant_of_hyperperiod is transparent
Expands to: Constant prosa.analysis.definitions.hyperperiod.starting_instant_of_hyperperiod
Declared in library prosa.analysis.definitions.hyperperiod, line 55, characters 13-44
@starting_instant_of_hyperperiod
     : forall Task : TaskType,
       TaskOffset Task -> PeriodicModel Task -> TaskSet (Equality.sort Task) -> instant -> nat
```

Body:

```coq
starting_instant_of_hyperperiod =
fun (Task : TaskType) (H : TaskOffset Task) (H0 : PeriodicModel Task) (ts : TaskSet (Equality.sort Task)) =>
let O_max := @max_task_offset Task H ts in
let HP := @hyperperiod Task H0 ts in fun t : instant => @hyperperiod_index Task H H0 ts t * HP + O_max
     : forall {Task : TaskType},
       TaskOffset Task -> PeriodicModel Task -> TaskSet (Equality.sort Task) -> instant -> nat

Arguments starting_instant_of_hyperperiod {Task H H0} ts t
```

## Lean

```lean
@Prosa.Analysis.Definitions.Hyperperiod.starting_instant_of_hyperperiod : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Offset.TaskOffset Task] →
      [Prosa.Model.Task.Arrival.Periodic.PeriodicModel Task] →
        Prosa.Model.Task.Concept.TaskSet Task → Prosa.Behavior.Time.instant → ℕ
```

Body:

```lean
def Prosa.Analysis.Definitions.Hyperperiod.starting_instant_of_hyperperiod.{u_1} : {Task :
    Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Offset.TaskOffset Task] →
      [Prosa.Model.Task.Arrival.Periodic.PeriodicModel Task] →
        Prosa.Model.Task.Concept.TaskSet Task → Prosa.Behavior.Time.instant → ℕ :=
fun {Task} [DecidableEq Task] [Prosa.Model.Task.Offset.TaskOffset Task]
    [Prosa.Model.Task.Arrival.Periodic.PeriodicModel Task] ts t =>
  Prosa.Analysis.Definitions.Hyperperiod.hyperperiod_index ts t *
      Prosa.Analysis.Definitions.Hyperperiod.hyperperiod ts +
    Prosa.Model.Task.Offset.max_task_offset ts
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Definitions_Hyperperiod_starting_instant_of_hyperperiod
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
Prosa_Analysis_Definitions_Hyperperiod_starting_instant_of_hyperperiod@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_3 : DecidableEq Task)
  (inst_6 : 
   Prosa_Model_Task_Offset_TaskOffset Task
     inst_3)
  (inst_9 : 
   Prosa_Model_Task_Arrival_Periodic_PeriodicModel Task
     inst_3)
  (ts : Prosa_Model_Task_Concept_TaskSet Task) (t : Prosa_Behavior_Time_instant) =>
HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat)
  (HMul_hMul_inst7 Nat Prosa_Behavior_Time_duration Nat (instHMul_inst1 Nat instMulNat)
     (Prosa_Analysis_Definitions_Hyperperiod_hyperperiod_index Task
        inst_3
        inst_6
        inst_9 ts t)
     (Prosa_Analysis_Definitions_Hyperperiod_hyperperiod Task
        inst_3
        inst_9 ts))
  (Prosa_Model_Task_Offset_max_task_offset Task
     inst_3
     inst_6 ts)
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Task_Offset_TaskOffset Task
         inst_3 ->
       Prosa_Model_Task_Arrival_Periodic_PeriodicModel Task
         inst_3 ->
       Prosa_Model_Task_Concept_TaskSet Task -> Prosa_Behavior_Time_instant -> Nat

Arguments Prosa_Analysis_Definitions_Hyperperiod_starting_instant_of_hyperperiod 
  Task inst_3
  inst_6
  inst_9 ts 
  t2
```
