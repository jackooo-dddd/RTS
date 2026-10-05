# `TaskMaxNonpreemptiveSegment`

- Kind (Rocq): Class
- Rocq: `prosa.model.task.preemption.parameters.TaskMaxNonpreemptiveSegment`
- Lean: `Prosa.Model.Task.Preemption.Parameters.TaskMaxNonpreemptiveSegment`
- Certificate: `TaskMaxNonpreemptiveSegment_source_total, TaskMaxNonpreemptiveSegment_target_total`

## Official Rocq

```coq
TaskMaxNonpreemptiveSegment : TaskType -> Type

TaskMaxNonpreemptiveSegment is not universe polymorphic
Arguments TaskMaxNonpreemptiveSegment Task
TaskMaxNonpreemptiveSegment is transparent
Expands to: Constant prosa.model.task.preemption.parameters.TaskMaxNonpreemptiveSegment
Declared in library prosa.model.task.preemption.parameters, line 16, characters 0-103
TaskMaxNonpreemptiveSegment
     : TaskType -> Type
```

Body:

```coq
TaskMaxNonpreemptiveSegment = fun Task : TaskType => Equality.sort Task -> work
     : TaskType -> Type

Arguments TaskMaxNonpreemptiveSegment Task
```

## Lean

```lean
Prosa.Model.Task.Preemption.Parameters.TaskMaxNonpreemptiveSegment : (Task : Prosa.Model.Task.Concept.TaskType) →
  [DecidableEq Task] → Type u_1
```

Body:

```lean
class Prosa.Model.Task.Preemption.Parameters.TaskMaxNonpreemptiveSegment.{u_1}
  (Task : Prosa.Model.Task.Concept.TaskType) [DecidableEq Task] : Type u_1
number of parameters: 2
fields:
  Prosa.Model.Task.Preemption.Parameters.TaskMaxNonpreemptiveSegment.task_max_nonpreemptive_segment : Task →
      Prosa.Behavior.Job.work
constructor:
  Prosa.Model.Task.Preemption.Parameters.TaskMaxNonpreemptiveSegment.mk.{u_1} {Task : Prosa.Model.Task.Concept.TaskType}
    [DecidableEq Task] (task_max_nonpreemptive_segment : Task → Prosa.Behavior.Job.work) :
    Prosa.Model.Task.Preemption.Parameters.TaskMaxNonpreemptiveSegment Task
```

## Lean, imported into Rocq

```coq
Prosa_Model_Task_Preemption_Parameters_TaskMaxNonpreemptiveSegment
     : forall Task : Prosa_Model_Task_Concept_TaskType, DecidableEq Task -> Type
```

Body:

```coq
Record
Prosa_Model_Task_Preemption_Parameters_TaskMaxNonpreemptiveSegment@{u_1 Lean.u_1+1.0 Lean.u_1+2.0}
    (Task : Prosa_Model_Task_Concept_TaskType)
(inst_3 : DecidableEq Task)
  : Type := Prosa_Model_Task_Preemption_Parameters_TaskMaxNonpreemptiveSegment_mk
  { task_max_nonpreemptive_segment : Task -> Prosa_Behavior_Job_work } as default_proj_id.

Prosa_Model_Task_Preemption_Parameters_TaskMaxNonpreemptiveSegment has primitive projections with eta conversion.
Arguments Prosa_Model_Task_Preemption_Parameters_TaskMaxNonpreemptiveSegment Task
  inst_3
Arguments Prosa_Model_Task_Preemption_Parameters_TaskMaxNonpreemptiveSegment_mk Task
  inst_3
  task_max_nonpreemptive_segment%_function_scope
```
