# `JobArrival`

- Kind (Rocq): Instance
- Rocq: `prosa.implementation.definitions.task.JobArrival`
- Lean: `Prosa.Implementation.Definitions.Task.JobArrival`
- Certificate: `JobArrival_correspondence`

## Official Rocq

```coq
JobArrival :
job.JobArrival (@reverse_coercion eqType Type task_concrete_job__canonical__eqtype_Equality concrete_job)

JobArrival is not universe polymorphic
JobArrival is transparent
Expands to: Constant prosa.implementation.definitions.task.JobArrival
Declared in library prosa.implementation.definitions.task, line 143, characters 2-72
JobArrival
     : job.JobArrival
         (@reverse_coercion eqType Type task_concrete_job__canonical__eqtype_Equality concrete_job)
```

Body:

```coq
JobArrival =
let Job := @reverse_coercion eqType Type task_concrete_job__canonical__eqtype_Equality concrete_job in
job_arrival
     : job.JobArrival
         (@reverse_coercion eqType Type task_concrete_job__canonical__eqtype_Equality concrete_job)
```

## Lean

```lean
Prosa.Implementation.Definitions.Task.JobArrival : Prosa.Behavior.Job.JobArrival
  Prosa.Implementation.Definitions.Task.concrete_job
```

Body:

```lean
@[instance_reducible] def Prosa.Implementation.Definitions.Task.JobArrival : Prosa.Behavior.Job.JobArrival
  Prosa.Implementation.Definitions.Task.concrete_job :=
{ job_arrival := Prosa.Implementation.Definitions.Task.concrete_job.job_arrival }
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Definitions_Task_JobArrival
     : Prosa_Behavior_Job_JobArrival_inst1 Prosa_Implementation_Definitions_Task_concrete_job
         Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_job
```

Body:

```coq
Prosa_Implementation_Definitions_Task_JobArrival@{} =
Prosa_Behavior_Job_JobArrival_mk_inst1 Prosa_Implementation_Definitions_Task_concrete_job
  Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_job
  Prosa_Implementation_Definitions_Task_concrete_job_job_arrival
     : Prosa_Behavior_Job_JobArrival_inst1 Prosa_Implementation_Definitions_Task_concrete_job
         Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_job
```
