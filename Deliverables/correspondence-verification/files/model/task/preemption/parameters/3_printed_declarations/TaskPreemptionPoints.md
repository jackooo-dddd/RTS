# `TaskPreemptionPoints`

- Kind (Rocq): Class
- Rocq: `prosa.model.task.preemption.parameters.TaskPreemptionPoints`
- Lean: `Prosa.Model.Task.Preemption.Parameters.TaskPreemptionPoints`
- Certificate: `TaskPreemptionPoints_source_total, TaskPreemptionPoints_target_total`

## Official Rocq

```coq
TaskPreemptionPoints : TaskType -> Type

TaskPreemptionPoints is not universe polymorphic
Arguments TaskPreemptionPoints Task
TaskPreemptionPoints is transparent
Expands to: Constant prosa.model.task.preemption.parameters.TaskPreemptionPoints
Declared in library prosa.model.task.preemption.parameters, line 28, characters 0-92
TaskPreemptionPoints
     : TaskType -> Type
```

Body:

```coq
TaskPreemptionPoints = fun Task : TaskType => Equality.sort Task -> seq work
     : TaskType -> Type

Arguments TaskPreemptionPoints Task
```

## Lean

```lean
Prosa.Model.Task.Preemption.Parameters.TaskPreemptionPoints : (Task : Prosa.Model.Task.Concept.TaskType) →
  [DecidableEq Task] → Type u_1
```

Body:

```lean
class Prosa.Model.Task.Preemption.Parameters.TaskPreemptionPoints.{u_1} (Task : Prosa.Model.Task.Concept.TaskType)
  [DecidableEq Task] : Type u_1
number of parameters: 2
fields:
  Prosa.Model.Task.Preemption.Parameters.TaskPreemptionPoints.task_preemption_points : Task →
      List Prosa.Behavior.Job.work
constructor:
  Prosa.Model.Task.Preemption.Parameters.TaskPreemptionPoints.mk.{u_1} {Task : Prosa.Model.Task.Concept.TaskType}
    [DecidableEq Task] (task_preemption_points : Task → List Prosa.Behavior.Job.work) :
    Prosa.Model.Task.Preemption.Parameters.TaskPreemptionPoints Task
```

## Lean, imported into Rocq

```coq
Prosa_Model_Task_Preemption_Parameters_TaskPreemptionPoints
     : forall Task : Prosa_Model_Task_Concept_TaskType, DecidableEq Task -> Type
```

Body:

```coq
Record
Prosa_Model_Task_Preemption_Parameters_TaskPreemptionPoints@{u_1 Lean.u_1+1.0 Lean.u_1+2.0}
    (Task : Prosa_Model_Task_Concept_TaskType)
(inst_3 : DecidableEq Task)
  : Type := Prosa_Model_Task_Preemption_Parameters_TaskPreemptionPoints_mk
  { task_preemption_points : Task -> List_inst1 Prosa_Behavior_Job_work } as default_proj_id.

Prosa_Model_Task_Preemption_Parameters_TaskPreemptionPoints has primitive projections with eta conversion.
Arguments Prosa_Model_Task_Preemption_Parameters_TaskPreemptionPoints Task
  inst_3
Arguments Prosa_Model_Task_Preemption_Parameters_TaskPreemptionPoints_mk Task
  inst_3
  task_preemption_points%_function_scope
```
