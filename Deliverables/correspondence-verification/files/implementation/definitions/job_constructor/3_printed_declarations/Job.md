# `Job`

- Kind (Rocq): Definition
- Rocq: `prosa.implementation.definitions.job_constructor.Job`
- Lean: `Prosa.Implementation.Definitions.JobConstructor.Job`
- Certificate: `Job_source_total, Job_target_total`

## Official Rocq

```coq
Job : eqType

Job is not universe polymorphic
Job is transparent
Expands to: Constant prosa.implementation.definitions.job_constructor.Job
Declared in library prosa.implementation.definitions.job_constructor, line 13, characters 11-14
Job
     : eqType
```

Body:

```coq
Job = @reverse_coercion eqType Type task_concrete_job__canonical__eqtype_Equality concrete_job
     : eqType
```

## Lean

```lean
Prosa.Implementation.Definitions.JobConstructor.Job : Type
```

Body:

```lean
@[reducible] def Prosa.Implementation.Definitions.JobConstructor.Job : Type :=
Prosa.Implementation.Definitions.Task.concrete_job
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Definitions_JobConstructor_Job
     : Type
```

Body:

```coq
Prosa_Implementation_Definitions_JobConstructor_Job@{} =
Prosa_Implementation_Definitions_Task_concrete_job
     : Type
```
