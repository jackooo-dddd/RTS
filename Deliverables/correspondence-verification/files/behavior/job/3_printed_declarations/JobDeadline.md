# `JobDeadline`

- Kind (Rocq): Class
- Rocq: `prosa.behavior.job.JobDeadline`
- Lean: `Prosa.Behavior.Job.JobDeadline`
- Certificate: ``

## Official Rocq

```coq
JobDeadline : JobType -> Type

JobDeadline is not universe polymorphic
Arguments JobDeadline Job
JobDeadline is transparent
Expands to: Constant prosa.behavior.job.JobDeadline
Declared in library prosa.behavior.job, line 24, characters 0-67
JobDeadline
     : JobType -> Type
```

## Lean

```lean
Prosa.Behavior.Job.JobDeadline : (Job : Prosa.Behavior.Job.JobType) → [DecidableEq Job] → Type u_1
```

## Lean, imported into Rocq

```coq
Prosa_Behavior_Job_JobDeadline
     : forall Job : Prosa_Behavior_Job_JobType, DecidableEq Job -> Type
```
