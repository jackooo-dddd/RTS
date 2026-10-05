# `TaskPriority`

- Kind (Rocq): Class
- Rocq: `prosa.model.priority.numeric_fixed_priority.TaskPriority`
- Lean: `Prosa.Model.Priority.NumericFixedPriority.TaskPriority`
- Certificate: `TaskPriority_source_total, TaskPriority_target_total`

## Official Rocq

```coq
TaskPriority : TaskType -> Type

TaskPriority is not universe polymorphic
Arguments TaskPriority Task
TaskPriority is transparent
Expands to: Constant prosa.model.priority.numeric_fixed_priority.TaskPriority
Declared in library prosa.model.priority.numeric_fixed_priority, line 12, characters 0-68
TaskPriority
     : TaskType -> Type
```

Body:

```coq
TaskPriority = fun Task : TaskType => Equality.sort Task -> nat
     : TaskType -> Type

Arguments TaskPriority Task
```

## Lean

```lean
Prosa.Model.Priority.NumericFixedPriority.TaskPriority : (Task : Prosa.Model.Task.Concept.TaskType) →
  [DecidableEq Task] → Type u_1
```

Body:

```lean
class Prosa.Model.Priority.NumericFixedPriority.TaskPriority.{u_1} (Task : Prosa.Model.Task.Concept.TaskType)
  [DecidableEq Task] : Type u_1
number of parameters: 2
fields:
  Prosa.Model.Priority.NumericFixedPriority.TaskPriority.task_priority : Task → ℕ
constructor:
  Prosa.Model.Priority.NumericFixedPriority.TaskPriority.mk.{u_1} {Task : Prosa.Model.Task.Concept.TaskType}
    [DecidableEq Task] (task_priority : Task → ℕ) : Prosa.Model.Priority.NumericFixedPriority.TaskPriority Task
```

## Lean, imported into Rocq

```coq
Prosa_Model_Priority_NumericFixedPriority_TaskPriority
     : forall Task : Prosa_Model_Task_Concept_TaskType, DecidableEq Task -> Type
```

Body:

```coq
Record
Prosa_Model_Priority_NumericFixedPriority_TaskPriority@{u_1 Lean.u_1+1.0 Lean.u_1+2.0}
    (Task : Prosa_Model_Task_Concept_TaskType)
(inst_3 : DecidableEq Task)
  : Type := Prosa_Model_Priority_NumericFixedPriority_TaskPriority_mk
  { task_priority : Task -> Nat } as default_proj_id.

Prosa_Model_Priority_NumericFixedPriority_TaskPriority has primitive projections with eta conversion.
Arguments Prosa_Model_Priority_NumericFixedPriority_TaskPriority Task
  inst_3
Arguments Prosa_Model_Priority_NumericFixedPriority_TaskPriority_mk Task
  inst_3
  task_priority%_function_scope
```
