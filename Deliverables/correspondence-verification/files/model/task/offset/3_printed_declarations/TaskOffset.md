# `TaskOffset`

- Kind (Rocq): Class
- Rocq: `prosa.model.task.offset.TaskOffset`
- Lean: `Prosa.Model.Task.Offset.TaskOffset`
- Certificate: `TaskOffset_source_total, TaskOffset_target_total`

## Official Rocq

```coq
TaskOffset : TaskType -> Type

TaskOffset is not universe polymorphic
Arguments TaskOffset Task
TaskOffset is transparent
Expands to: Constant prosa.model.task.offset.TaskOffset
Declared in library prosa.model.task.offset, line 11, characters 0-68
TaskOffset
     : TaskType -> Type
```

Body:

```coq
TaskOffset = fun Task : TaskType => Equality.sort Task -> instant
     : TaskType -> Type

Arguments TaskOffset Task
```

## Lean

```lean
Prosa.Model.Task.Offset.TaskOffset : (Task : Prosa.Model.Task.Concept.TaskType) → [DecidableEq Task] → Type u_1
```

Body:

```lean
class Prosa.Model.Task.Offset.TaskOffset.{u_1} (Task : Prosa.Model.Task.Concept.TaskType) [DecidableEq Task] : Type u_1
number of parameters: 2
fields:
  Prosa.Model.Task.Offset.TaskOffset.task_offset : Task → Prosa.Behavior.Time.instant
constructor:
  Prosa.Model.Task.Offset.TaskOffset.mk.{u_1} {Task : Prosa.Model.Task.Concept.TaskType} [DecidableEq Task]
    (task_offset : Task → Prosa.Behavior.Time.instant) : Prosa.Model.Task.Offset.TaskOffset Task
```

## Lean, imported into Rocq

```coq
Prosa_Model_Task_Offset_TaskOffset
     : forall Task : Prosa_Model_Task_Concept_TaskType, DecidableEq Task -> Type
```

Body:

```coq
Record
Prosa_Model_Task_Offset_TaskOffset@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} (Task : Prosa_Model_Task_Concept_TaskType)
(inst_3 : DecidableEq Task)
  : Type := Prosa_Model_Task_Offset_TaskOffset_mk
  { task_offset : Task -> Prosa_Behavior_Time_instant } as default_proj_id.

Prosa_Model_Task_Offset_TaskOffset has primitive projections with eta conversion.
Arguments Prosa_Model_Task_Offset_TaskOffset Task
  inst_3
Arguments Prosa_Model_Task_Offset_TaskOffset_mk Task
  inst_3 task_offset%_function_scope
```
