# `JobArrival`

- Kind (Rocq): Class
- Rocq: `prosa.behavior.job.JobArrival`
- Lean: `Prosa.Behavior.Job.JobArrival`
- Certificate: ``

## Official Rocq

```coq
JobArrival : JobType -> Type

JobArrival is not universe polymorphic
Arguments JobArrival Job
JobArrival is transparent
Expands to: Constant prosa.behavior.job.JobArrival
Declared in library prosa.behavior.job, line 21, characters 0-65
JobArrival
     : JobType -> Type
```

## Lean

```lean
Prosa.Behavior.Job.JobArrival : (Job : Prosa.Behavior.Job.JobType) → [DecidableEq Job] → Type u_1
```

## Lean, imported into Rocq

```coq
Prosa_Behavior_Job_JobArrival
     : forall Job : Prosa_Behavior_Job_JobType, DecidableEq Job -> Type
```
