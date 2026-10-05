# `PeriodicModel`

- Kind (Rocq): Class
- Rocq: `prosa.model.task.arrival.periodic.PeriodicModel`
- Lean: `Prosa.Model.Task.Arrival.Periodic.PeriodicModel`
- Certificate: `PeriodicModel_source_total, PeriodicModel_target_total`

## Official Rocq

```coq
PeriodicModel : TaskType -> Type

PeriodicModel is not universe polymorphic
Arguments PeriodicModel Task
PeriodicModel is transparent
Expands to: Constant prosa.model.task.arrival.periodic.PeriodicModel
Declared in library prosa.model.task.arrival.periodic, line 18, characters 0-72
PeriodicModel
     : TaskType -> Type
```

Body:

```coq
PeriodicModel = fun Task : TaskType => Equality.sort Task -> duration
     : TaskType -> Type

Arguments PeriodicModel Task
```

## Lean

```lean
Prosa.Model.Task.Arrival.Periodic.PeriodicModel : (Task : Prosa.Model.Task.Concept.TaskType) →
  [DecidableEq Task] → Type u_1
```

Body:

```lean
class Prosa.Model.Task.Arrival.Periodic.PeriodicModel.{u_1} (Task : Prosa.Model.Task.Concept.TaskType)
  [DecidableEq Task] : Type u_1
number of parameters: 2
fields:
  Prosa.Model.Task.Arrival.Periodic.PeriodicModel.task_period : Task → Prosa.Behavior.Time.duration
constructor:
  Prosa.Model.Task.Arrival.Periodic.PeriodicModel.mk.{u_1} {Task : Prosa.Model.Task.Concept.TaskType} [DecidableEq Task]
    (task_period : Task → Prosa.Behavior.Time.duration) : Prosa.Model.Task.Arrival.Periodic.PeriodicModel Task
```

## Lean, imported into Rocq

```coq
Prosa_Model_Task_Arrival_Periodic_PeriodicModel
     : forall Task : Prosa_Model_Task_Concept_TaskType, DecidableEq Task -> Type
```

Body:

```coq
Record
Prosa_Model_Task_Arrival_Periodic_PeriodicModel@{u_1 Lean.u_1+1.0 Lean.u_1+2.0}
    (Task : Prosa_Model_Task_Concept_TaskType)
(inst_3 : DecidableEq Task)
  : Type := Prosa_Model_Task_Arrival_Periodic_PeriodicModel_mk
  { task_period : Task -> Prosa_Behavior_Time_duration } as default_proj_id.

Prosa_Model_Task_Arrival_Periodic_PeriodicModel has primitive projections with eta conversion.
Arguments Prosa_Model_Task_Arrival_Periodic_PeriodicModel Task
  inst_3
Arguments Prosa_Model_Task_Arrival_Periodic_PeriodicModel_mk Task
  inst_3 task_period%_function_scope
```
