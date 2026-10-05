# `Job`

- Kind (Rocq): Definition
- Rocq: `prosa.implementation.refinements.FP.preemptive_sched.Job`
- Lean: `Prosa.Implementation.Refinements.FP.PreemptiveSched.Job`
- Certificate: `Job_source_total, Job_target_total`

## Official Rocq

```coq
Job : eqType

Job is not universe polymorphic
Job is transparent
Expands to: Constant prosa.implementation.refinements.FP.preemptive_sched.Job
Declared in library prosa.implementation.refinements.FP.preemptive_sched, line 20, characters 13-16
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
Prosa.Implementation.Refinements.FP.PreemptiveSched.Job : Type
```

Body:

```lean
@[reducible] def Prosa.Implementation.Refinements.FP.PreemptiveSched.Job : Type :=
Prosa.Implementation.Definitions.Task.concrete_job
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_FP_PreemptiveSched_Job
     : Type
```

Body:

```coq
Prosa_Implementation_Refinements_FP_PreemptiveSched_Job@{} =
Prosa_Implementation_Definitions_Task_concrete_job
     : Type
```
