# `task_offsets`

- Kind (Rocq): Definition
- Rocq: `prosa.model.task.offset.task_offsets`
- Lean: `Prosa.Model.Task.Offset.task_offsets`
- Certificate: `task_offsets_correspondence`

## Official Rocq

```coq
task_offsets : forall {Task : TaskType}, TaskOffset Task -> TaskSet (Equality.sort Task) -> seq instant

task_offsets is not universe polymorphic
Arguments task_offsets {Task H} ts
task_offsets is transparent
Expands to: Constant prosa.model.task.offset.task_offsets
Declared in library prosa.model.task.offset, line 65, characters 13-25
@task_offsets
     : forall Task : TaskType, TaskOffset Task -> TaskSet (Equality.sort Task) -> seq instant
```

Body:

```coq
task_offsets =
fun (Task : TaskType) (H : TaskOffset Task) => [eta @map (Equality.sort Task) instant (@task_offset Task H)]
     : forall {Task : TaskType}, TaskOffset Task -> TaskSet (Equality.sort Task) -> seq instant

Arguments task_offsets {Task H} ts
```

## Lean

```lean
@Prosa.Model.Task.Offset.task_offsets : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Offset.TaskOffset Task] → Prosa.Model.Task.Concept.TaskSet Task → List Prosa.Behavior.Time.instant
```

Body:

```lean
def Prosa.Model.Task.Offset.task_offsets.{u_1} : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Offset.TaskOffset Task] →
      Prosa.Model.Task.Concept.TaskSet Task → List Prosa.Behavior.Time.instant :=
fun {Task} [DecidableEq Task] [Prosa.Model.Task.Offset.TaskOffset Task] ts =>
  List.map Prosa.Model.Task.Offset.task_offset ts
```

## Lean, imported into Rocq

```coq
Prosa_Model_Task_Offset_task_offsets
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Task_Offset_TaskOffset Task inst_3 ->
       Prosa_Model_Task_Concept_TaskSet Task -> List_inst1 Prosa_Behavior_Time_instant
```

Body:

```coq
Prosa_Model_Task_Offset_task_offsets@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_3 : DecidableEq Task)
  (inst_6 : Prosa_Model_Task_Offset_TaskOffset Task
                                                                   inst_3)
  (ts : Prosa_Model_Task_Concept_TaskSet Task) =>
List_map_inst2 Task Prosa_Behavior_Time_instant
  (Prosa_Model_Task_Offset_TaskOffset_task_offset Task
     inst_3
     inst_6)
  ts
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Task_Offset_TaskOffset Task inst_3 ->
       Prosa_Model_Task_Concept_TaskSet Task -> List_inst1 Prosa_Behavior_Time_instant

Arguments Prosa_Model_Task_Offset_task_offsets Task
  inst_3
  inst_6 ts
```
