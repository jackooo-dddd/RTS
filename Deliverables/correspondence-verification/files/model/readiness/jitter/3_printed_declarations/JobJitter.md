# `JobJitter`

- Kind (Rocq): Class
- Rocq: `prosa.model.readiness.jitter.JobJitter`
- Lean: `Prosa.Model.Readiness.Jitter.JobJitter`
- Certificate: `JobJitter_source_total, JobJitter_target_total, JobJitter_source_roundtrip`

## Official Rocq

```coq
JobJitter : JobType -> Type

JobJitter is not universe polymorphic
Arguments JobJitter Job
JobJitter is transparent
Expands to: Constant prosa.model.readiness.jitter.JobJitter
Declared in library prosa.model.readiness.jitter, line 12, characters 0-64
JobJitter
     : JobType -> Type
```

## Lean

```lean
Prosa.Model.Readiness.Jitter.JobJitter : (Job : Prosa.Behavior.Job.JobType) → [DecidableEq Job] → Type u_1
```

## Lean, imported into Rocq

```coq
Prosa_Model_Readiness_Jitter_JobJitter
     : forall Job : Prosa_Behavior_Job_JobType, DecidableEq Job -> Type
```
