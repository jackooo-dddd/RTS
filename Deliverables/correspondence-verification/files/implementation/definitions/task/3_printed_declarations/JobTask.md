# `JobTask`

- Kind (Rocq): Instance
- Rocq: `prosa.implementation.definitions.task.JobTask`
- Lean: `Prosa.Implementation.Definitions.Task.JobTask`
- Certificate: `JobTask_correspondence`

## Official Rocq

```coq
JobTask :
concept.JobTask (@reverse_coercion eqType Type task_concrete_job__canonical__eqtype_Equality concrete_job)
  (@reverse_coercion eqType Type task_concrete_task__canonical__eqtype_Equality concrete_task)

JobTask is not universe polymorphic
JobTask is transparent
Expands to: Constant prosa.implementation.definitions.task.JobTask
Declared in library prosa.implementation.definitions.task, line 142, characters 2-68
JobTask
     : concept.JobTask
         (@reverse_coercion eqType Type task_concrete_job__canonical__eqtype_Equality concrete_job)
         (@reverse_coercion eqType Type task_concrete_task__canonical__eqtype_Equality concrete_task)
```

Body:

```coq
JobTask =
let Task := @reverse_coercion eqType Type task_concrete_task__canonical__eqtype_Equality concrete_task in
let Job := @reverse_coercion eqType Type task_concrete_job__canonical__eqtype_Equality concrete_job in
job_task
     : concept.JobTask
         (@reverse_coercion eqType Type task_concrete_job__canonical__eqtype_Equality concrete_job)
         (@reverse_coercion eqType Type task_concrete_task__canonical__eqtype_Equality concrete_task)
```

## Lean

```lean
Prosa.Implementation.Definitions.Task.JobTask : Prosa.Model.Task.Concept.JobTask
  Prosa.Implementation.Definitions.Task.concrete_job Prosa.Implementation.Definitions.Task.concrete_task
```

Body:

```lean
@[instance_reducible] def Prosa.Implementation.Definitions.Task.JobTask : Prosa.Model.Task.Concept.JobTask
  Prosa.Implementation.Definitions.Task.concrete_job Prosa.Implementation.Definitions.Task.concrete_task :=
{ job_task := Prosa.Implementation.Definitions.Task.concrete_job.job_task }
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Definitions_Task_JobTask
     : Prosa_Model_Task_Concept_JobTask_inst3 Prosa_Implementation_Definitions_Task_concrete_job
         Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_job
         Prosa_Implementation_Definitions_Task_concrete_task
         Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_task
```

Body:

```coq
Prosa_Implementation_Definitions_Task_JobTask@{} =
Prosa_Model_Task_Concept_JobTask_mk_inst3 Prosa_Implementation_Definitions_Task_concrete_job
  Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_job
  Prosa_Implementation_Definitions_Task_concrete_task
  Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_task
  Prosa_Implementation_Definitions_Task_concrete_job_job_task
     : Prosa_Model_Task_Concept_JobTask_inst3 Prosa_Implementation_Definitions_Task_concrete_job
         Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_job
         Prosa_Implementation_Definitions_Task_concrete_task
         Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_task
```
