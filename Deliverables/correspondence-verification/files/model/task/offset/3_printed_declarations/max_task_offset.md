# `max_task_offset`

- Kind (Rocq): Definition
- Rocq: `prosa.model.task.offset.max_task_offset`
- Lean: `Prosa.Model.Task.Offset.max_task_offset`
- Certificate: `max_task_offset_correspondence`

## Official Rocq

```coq
max_task_offset : forall {Task : TaskType}, TaskOffset Task -> TaskSet (Equality.sort Task) -> nat

max_task_offset is not universe polymorphic
Arguments max_task_offset {Task H} ts
max_task_offset is transparent
Expands to: Constant prosa.model.task.offset.max_task_offset
Declared in library prosa.model.task.offset, line 68, characters 13-28
@max_task_offset
     : forall Task : TaskType, TaskOffset Task -> TaskSet (Equality.sort Task) -> nat
```

Body:

```coq
max_task_offset =
fun (Task : TaskType) (H : TaskOffset Task) (ts : TaskSet (Equality.sort Task)) =>
max0 (@task_offsets Task H ts)
     : forall {Task : TaskType}, TaskOffset Task -> TaskSet (Equality.sort Task) -> nat

Arguments max_task_offset {Task H} ts
```

## Lean

```lean
@Prosa.Model.Task.Offset.max_task_offset : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] → [Prosa.Model.Task.Offset.TaskOffset Task] → Prosa.Model.Task.Concept.TaskSet Task → ℕ
```

Body:

```lean
def Prosa.Model.Task.Offset.max_task_offset.{u_1} : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] → [Prosa.Model.Task.Offset.TaskOffset Task] → Prosa.Model.Task.Concept.TaskSet Task → ℕ :=
fun {Task} [DecidableEq Task] [Prosa.Model.Task.Offset.TaskOffset Task] ts =>
  Prosa.Util.List.max0 (Prosa.Model.Task.Offset.task_offsets ts)
```

## Lean, imported into Rocq

```coq
Prosa_Model_Task_Offset_max_task_offset
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Task_Offset_TaskOffset Task inst_3 ->
       Prosa_Model_Task_Concept_TaskSet Task -> Nat
```

Body:

```coq
Prosa_Model_Task_Offset_max_task_offset@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_3 : DecidableEq Task)
  (inst_6 : Prosa_Model_Task_Offset_TaskOffset Task
                                                                   inst_3)
  (ts : Prosa_Model_Task_Concept_TaskSet Task) =>
Prosa_Util_List_max0
  (Prosa_Model_Task_Offset_task_offsets Task inst_3
     inst_6 ts)
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Task_Offset_TaskOffset Task inst_3 ->
       Prosa_Model_Task_Concept_TaskSet Task -> Nat

Arguments Prosa_Model_Task_Offset_max_task_offset Task
  inst_3
  inst_6 ts
```
