# `TaskRunToCompletionThreshold`

- Kind (Rocq): Class
- Rocq: `prosa.model.task.preemption.parameters.TaskRunToCompletionThreshold`
- Lean: `Prosa.Model.Task.Preemption.Parameters.TaskRunToCompletionThreshold`
- Certificate: `TaskRunToCompletionThreshold_source_total, TaskRunToCompletionThreshold_target_total`

## Official Rocq

```coq
TaskRunToCompletionThreshold : TaskType -> Type

TaskRunToCompletionThreshold is not universe polymorphic
Arguments TaskRunToCompletionThreshold Task
TaskRunToCompletionThreshold is transparent
Expands to: Constant prosa.model.task.preemption.parameters.TaskRunToCompletionThreshold
Declared in library prosa.model.task.preemption.parameters, line 23, characters 0-83
TaskRunToCompletionThreshold
     : TaskType -> Type
```

Body:

```coq
TaskRunToCompletionThreshold = fun Task : TaskType => Equality.sort Task -> work
     : TaskType -> Type

Arguments TaskRunToCompletionThreshold Task
```

## Lean

```lean
Prosa.Model.Task.Preemption.Parameters.TaskRunToCompletionThreshold : (Task : Prosa.Model.Task.Concept.TaskType) →
  [DecidableEq Task] → Type u_1
```

Body:

```lean
class Prosa.Model.Task.Preemption.Parameters.TaskRunToCompletionThreshold.{u_1}
  (Task : Prosa.Model.Task.Concept.TaskType) [DecidableEq Task] : Type u_1
number of parameters: 2
fields:
  Prosa.Model.Task.Preemption.Parameters.TaskRunToCompletionThreshold.task_rtct : Task → Prosa.Behavior.Job.work
constructor:
  Prosa.Model.Task.Preemption.Parameters.TaskRunToCompletionThreshold.mk.{u_1}
    {Task : Prosa.Model.Task.Concept.TaskType} [DecidableEq Task] (task_rtct : Task → Prosa.Behavior.Job.work) :
    Prosa.Model.Task.Preemption.Parameters.TaskRunToCompletionThreshold Task
```

## Lean, imported into Rocq

```coq
Prosa_Model_Task_Preemption_Parameters_TaskRunToCompletionThreshold
     : forall Task : Prosa_Model_Task_Concept_TaskType, DecidableEq Task -> Type
```

Body:

```coq
Record
Prosa_Model_Task_Preemption_Parameters_TaskRunToCompletionThreshold@{u_1 Lean.u_1+1.0 Lean.u_1+2.0}
    (Task : Prosa_Model_Task_Concept_TaskType)
(inst_3 : DecidableEq Task)
  : Type := Prosa_Model_Task_Preemption_Parameters_TaskRunToCompletionThreshold_mk
  { task_rtct : Task -> Prosa_Behavior_Job_work } as default_proj_id.

Prosa_Model_Task_Preemption_Parameters_TaskRunToCompletionThreshold has primitive projections with eta conversion.
Arguments Prosa_Model_Task_Preemption_Parameters_TaskRunToCompletionThreshold Task
  inst_3
Arguments Prosa_Model_Task_Preemption_Parameters_TaskRunToCompletionThreshold_mk 
  Task inst_3 
  task_rtct%_function_scope
```
