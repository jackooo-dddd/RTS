# `concrete_job`

- Kind (Rocq): Record
- Rocq: `prosa.implementation.definitions.task.concrete_job`
- Lean: `Prosa.Implementation.Definitions.Task.concrete_job`
- Certificate: `concrete_job_source_total, concrete_job_target_total`

## Official Rocq

```coq
concrete_job : Type

concrete_job is not universe polymorphic
Expands to: Inductive prosa.implementation.definitions.task.concrete_job
Declared in library prosa.implementation.definitions.task, line 66, characters 7-19
concrete_job
     : Type
```

Body:

```coq
Record concrete_job : Type := Build_concrete_job
  { job_id : nat;
    job_arrival : instant;
    job_cost : nat;
    job_deadline : instant;
    job_task : Equality.sort
                 (@reverse_coercion eqType Type task_concrete_task__canonical__eqtype_Equality concrete_task
                  :
                  eqType) }.

Arguments Build_concrete_job job_id%nat_scope job_arrival job_cost%nat_scope job_deadline job_task
Arguments job_id c
Arguments job_arrival c
Arguments job_cost c
Arguments job_deadline c
Arguments job_task c
```

## Lean

```lean
Prosa.Implementation.Definitions.Task.concrete_job : Type
```

Body:

```lean
structure Prosa.Implementation.Definitions.Task.concrete_job : Type
number of parameters: 0
fields:
  Prosa.Implementation.Definitions.Task.concrete_job.job_id : ℕ
  Prosa.Implementation.Definitions.Task.concrete_job.job_arrival : Prosa.Behavior.Time.instant
  Prosa.Implementation.Definitions.Task.concrete_job.job_cost : ℕ
  Prosa.Implementation.Definitions.Task.concrete_job.job_deadline : Prosa.Behavior.Time.instant
  Prosa.Implementation.Definitions.Task.concrete_job.job_task : Prosa.Implementation.Definitions.Task.concrete_task
constructor:
  Prosa.Implementation.Definitions.Task.concrete_job.mk (job_id : ℕ) (job_arrival : Prosa.Behavior.Time.instant)
    (job_cost : ℕ) (job_deadline : Prosa.Behavior.Time.instant)
    (job_task : Prosa.Implementation.Definitions.Task.concrete_task) :
    Prosa.Implementation.Definitions.Task.concrete_job
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Definitions_Task_concrete_job
     : Type
```

Body:

```coq
Record
Prosa_Implementation_Definitions_Task_concrete_job@{}
    : Type := Prosa_Implementation_Definitions_Task_concrete_job_mk
  { job_id : Nat;
    job_arrival0 : Prosa_Behavior_Time_instant;
    job_cost0 : Nat;
    job_deadline0 : Prosa_Behavior_Time_instant;
    job_task0 : Prosa_Implementation_Definitions_Task_concrete_task } as default_proj_id.

Prosa_Implementation_Definitions_Task_concrete_job has primitive projections with eta conversion.
Arguments Prosa_Implementation_Definitions_Task_concrete_job_mk job_id%_Nat_scope 
  job_arrival0 job_cost0%_Nat_scope job_deadline0 job_task0
```
