# `TaskTotalSuspension`

- Kind (Rocq): Class
- Rocq: `prosa.model.task.suspension.dynamic.TaskTotalSuspension`
- Lean: `Prosa.Model.Task.Suspension.Dynamic.TaskTotalSuspension`
- Certificate: `TaskTotalSuspension_source_total, TaskTotalSuspension_target_total`

## Official Rocq

```coq
TaskTotalSuspension : TaskType -> Type

TaskTotalSuspension is not universe polymorphic
Arguments TaskTotalSuspension Task
TaskTotalSuspension is transparent
Expands to: Constant prosa.model.task.suspension.dynamic.TaskTotalSuspension
Declared in library prosa.model.task.suspension.dynamic, line 9, characters 0-88
TaskTotalSuspension
     : TaskType -> Type
```

Body:

```coq
TaskTotalSuspension = fun Task : TaskType => Equality.sort Task -> duration
     : TaskType -> Type

Arguments TaskTotalSuspension Task
```

## Lean

```lean
Prosa.Model.Task.Suspension.Dynamic.TaskTotalSuspension : (Task : Prosa.Model.Task.Concept.TaskType) →
  [DecidableEq Task] → Type u_1
```

Body:

```lean
class Prosa.Model.Task.Suspension.Dynamic.TaskTotalSuspension.{u_1} (Task : Prosa.Model.Task.Concept.TaskType)
  [DecidableEq Task] : Type u_1
number of parameters: 2
fields:
  Prosa.Model.Task.Suspension.Dynamic.TaskTotalSuspension.task_total_suspension : Task → Prosa.Behavior.Time.duration
constructor:
  Prosa.Model.Task.Suspension.Dynamic.TaskTotalSuspension.mk.{u_1} {Task : Prosa.Model.Task.Concept.TaskType}
    [DecidableEq Task] (task_total_suspension : Task → Prosa.Behavior.Time.duration) :
    Prosa.Model.Task.Suspension.Dynamic.TaskTotalSuspension Task
```

## Lean, imported into Rocq

```coq
Prosa_Model_Task_Suspension_Dynamic_TaskTotalSuspension
     : forall Task : Prosa_Model_Task_Concept_TaskType, DecidableEq Task -> Type
```

Body:

```coq
Record
Prosa_Model_Task_Suspension_Dynamic_TaskTotalSuspension@{u_1 Lean.u_1+1.0 Lean.u_1+2.0}
    (Task : Prosa_Model_Task_Concept_TaskType)
(inst_3 : DecidableEq Task)
  : Type := Prosa_Model_Task_Suspension_Dynamic_TaskTotalSuspension_mk
  { task_total_suspension : Task -> Prosa_Behavior_Time_duration } as default_proj_id.

Prosa_Model_Task_Suspension_Dynamic_TaskTotalSuspension has primitive projections with eta conversion.
Arguments Prosa_Model_Task_Suspension_Dynamic_TaskTotalSuspension Task
  inst_3
Arguments Prosa_Model_Task_Suspension_Dynamic_TaskTotalSuspension_mk Task
  inst_3 task_total_suspension%_function_scope
```
