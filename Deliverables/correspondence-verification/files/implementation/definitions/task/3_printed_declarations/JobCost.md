# `JobCost`

- Kind (Rocq): Instance
- Rocq: `prosa.implementation.definitions.task.JobCost`
- Lean: `Prosa.Implementation.Definitions.Task.JobCost`
- Certificate: `JobCost_correspondence`

## Official Rocq

```coq
JobCost :
job.JobCost (@reverse_coercion eqType Type task_concrete_job__canonical__eqtype_Equality concrete_job)

JobCost is not universe polymorphic
JobCost is transparent
Expands to: Constant prosa.implementation.definitions.task.JobCost
Declared in library prosa.implementation.definitions.task, line 144, characters 2-63
JobCost
     : job.JobCost (@reverse_coercion eqType Type task_concrete_job__canonical__eqtype_Equality concrete_job)
```

Body:

```coq
JobCost =
let Job := @reverse_coercion eqType Type task_concrete_job__canonical__eqtype_Equality concrete_job in
job_cost
     : job.JobCost (@reverse_coercion eqType Type task_concrete_job__canonical__eqtype_Equality concrete_job)
```

## Lean

```lean
Prosa.Implementation.Definitions.Task.JobCost : Prosa.Behavior.Job.JobCost
  Prosa.Implementation.Definitions.Task.concrete_job
```

Body:

```lean
@[instance_reducible] def Prosa.Implementation.Definitions.Task.JobCost : Prosa.Behavior.Job.JobCost
  Prosa.Implementation.Definitions.Task.concrete_job :=
{ job_cost := Prosa.Implementation.Definitions.Task.concrete_job.job_cost }
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Definitions_Task_JobCost
     : Prosa_Behavior_Job_JobCost_inst1 Prosa_Implementation_Definitions_Task_concrete_job
         Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_job
```

Body:

```coq
Prosa_Implementation_Definitions_Task_JobCost@{} =
Prosa_Behavior_Job_JobCost_mk_inst1 Prosa_Implementation_Definitions_Task_concrete_job
  Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_job
  Prosa_Implementation_Definitions_Task_concrete_job_job_cost
     : Prosa_Behavior_Job_JobCost_inst1 Prosa_Implementation_Definitions_Task_concrete_job
         Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_job
```
