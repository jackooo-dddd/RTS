# `JobDelay`

- Kind (Rocq): Class
- Rocq: `prosa.results.transfer_schedulability.paper_model.JobDelay`
- Lean: `Prosa.Results.TransferSchedulability.PaperModel.JobDelay`
- Certificate: `JobDelay_source_total, JobDelay_target_total`

## Official Rocq

```coq
JobDelay : JobType -> Type

JobDelay is not universe polymorphic
Arguments JobDelay Job
Expands to: Inductive prosa.results.transfer_schedulability.paper_model.JobDelay
Declared in library prosa.results.transfer_schedulability.paper_model, line 47, characters 6-14
JobDelay
     : JobType -> Type
```

Body:

```coq
Record JobDelay (Job : JobType) : Type := Build_JobDelay
  { job_delay : Equality.sort Job -> Equality.sort Job -> duration }.

Arguments JobDelay Job
Arguments Build_JobDelay Job job_delay%function_scope
Arguments job_delay {Job JobDelay} _ _
```

## Lean

```lean
Prosa.Results.TransferSchedulability.PaperModel.JobDelay : (Job : Prosa.Behavior.Job.JobType) →
  [DecidableEq Job] → Type u_1
```

Body:

```lean
class Prosa.Results.TransferSchedulability.PaperModel.JobDelay.{u_1} (Job : Prosa.Behavior.Job.JobType)
  [DecidableEq Job] : Type u_1
number of parameters: 2
fields:
  Prosa.Results.TransferSchedulability.PaperModel.JobDelay.job_delay : Job → Job → Prosa.Behavior.Time.duration
constructor:
  Prosa.Results.TransferSchedulability.PaperModel.JobDelay.mk.{u_1} {Job : Prosa.Behavior.Job.JobType} [DecidableEq Job]
    (job_delay : Job → Job → Prosa.Behavior.Time.duration) :
    Prosa.Results.TransferSchedulability.PaperModel.JobDelay Job
```

## Lean, imported into Rocq

```coq
Prosa_Results_TransferSchedulability_PaperModel_JobDelay
     : forall Job : Prosa_Behavior_Job_JobType, DecidableEq Job -> Type
```

Body:

```coq
Record
Prosa_Results_TransferSchedulability_PaperModel_JobDelay@{u_1 Lean.u_1+1.0 Lean.u_1+2.0}
    (Job : Prosa_Behavior_Job_JobType)
(inst_3 : DecidableEq Job)
  : Type := Prosa_Results_TransferSchedulability_PaperModel_JobDelay_mk
  { job_delay : Job -> Job -> Prosa_Behavior_Time_duration } as default_proj_id.

Prosa_Results_TransferSchedulability_PaperModel_JobDelay has primitive projections with eta conversion.
Arguments Prosa_Results_TransferSchedulability_PaperModel_JobDelay Job
  inst_3
Arguments Prosa_Results_TransferSchedulability_PaperModel_JobDelay_mk Job
  inst_3 job_delay%_function_scope
```
