# `JobType`

- Kind (Rocq): Definition
- Rocq: `prosa.behavior.job.JobType`
- Lean: `Prosa.Behavior.Job.JobType`
- Certificate: ``

## Official Rocq

```coq
JobType : Type

JobType is not universe polymorphic
JobType is transparent
Expands to: Constant prosa.behavior.job.JobType
Declared in library prosa.behavior.job, line 7, characters 11-18
JobType
     : Type
```

Body:

```coq
JobType = eqType
     : Type
```

## Lean

```lean
Prosa.Behavior.Job.JobType : Type (u_1 + 1)
@[reducible] def Prosa.Behavior.Job.JobType.{u} : Type (u + 1) :=
Type u
```

## Lean, imported into Rocq

```coq
Prosa_Behavior_Job_JobType
     : Type
```

Body:

```coq
Prosa_Behavior_Job_JobType@{u Lean.u+1.0 Lean.u+2.0} = Type
     : Type
```
