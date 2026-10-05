# `PriorityPoint`

- Kind (Rocq): Class
- Rocq: `prosa.model.priority.gel.PriorityPoint`
- Lean: `Prosa.Model.Priority.Gel.PriorityPoint`
- Certificate: `PriorityPoint_source_total, PriorityPoint_target_total`

## Official Rocq

```coq
PriorityPoint : TaskType -> Type

PriorityPoint is not universe polymorphic
Arguments PriorityPoint Task
PriorityPoint is transparent
Expands to: Constant prosa.model.priority.gel.PriorityPoint
Declared in library prosa.model.priority.gel, line 24, characters 0-78
PriorityPoint
     : TaskType -> Type
```

Body:

```coq
PriorityPoint = fun Task : TaskType => Equality.sort Task -> offset
     : TaskType -> Type

Arguments PriorityPoint Task
```

## Lean

```lean
Prosa.Model.Priority.Gel.PriorityPoint : (Task : Prosa.Model.Task.Concept.TaskType) → [DecidableEq Task] → Type u_1
```

Body:

```lean
class Prosa.Model.Priority.Gel.PriorityPoint.{u_1} (Task : Prosa.Model.Task.Concept.TaskType) [DecidableEq Task] :
  Type u_1
number of parameters: 2
fields:
  Prosa.Model.Priority.Gel.PriorityPoint.task_priority_point : Task → Prosa.Model.Priority.Gel.offset
constructor:
  Prosa.Model.Priority.Gel.PriorityPoint.mk.{u_1} {Task : Prosa.Model.Task.Concept.TaskType} [DecidableEq Task]
    (task_priority_point : Task → Prosa.Model.Priority.Gel.offset) : Prosa.Model.Priority.Gel.PriorityPoint Task
```

## Lean, imported into Rocq

```coq
Prosa_Model_Priority_Gel_PriorityPoint
     : forall Task : Prosa_Model_Task_Concept_TaskType, DecidableEq Task -> Type
```

Body:

```coq
Record
Prosa_Model_Priority_Gel_PriorityPoint@{u_1 Lean.u_1+1.0 Lean.u_1+2.0}
    (Task : Prosa_Model_Task_Concept_TaskType)
(inst_3 : DecidableEq Task)
  : Type := Prosa_Model_Priority_Gel_PriorityPoint_mk
  { task_priority_point : Task -> Prosa_Model_Priority_Gel_offset } as default_proj_id.

Prosa_Model_Priority_Gel_PriorityPoint has primitive projections with eta conversion.
Arguments Prosa_Model_Priority_Gel_PriorityPoint Task
  inst_3
Arguments Prosa_Model_Priority_Gel_PriorityPoint_mk Task
  inst_3 task_priority_point%_function_scope
```
