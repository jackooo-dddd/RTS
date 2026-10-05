# `JobCost`

- Kind (Rocq): Class
- Rocq: `prosa.behavior.job.JobCost`
- Lean: `Prosa.Behavior.Job.JobCost`
- Certificate: ``

## Official Rocq

```coq
JobCost : JobType -> Type

JobCost is not universe polymorphic
Arguments JobCost Job
JobCost is transparent
Expands to: Constant prosa.behavior.job.JobCost
Declared in library prosa.behavior.job, line 18, characters 0-56
JobCost
     : JobType -> Type
```

## Lean

```lean
Prosa.Behavior.Job.JobCost : (Job : Prosa.Behavior.Job.JobType) → [DecidableEq Job] → Type u_1
```

## Lean, imported into Rocq

```coq
Prosa_Behavior_Job_JobCost
     : forall Job : Prosa_Behavior_Job_JobType, DecidableEq Job -> Type
```
