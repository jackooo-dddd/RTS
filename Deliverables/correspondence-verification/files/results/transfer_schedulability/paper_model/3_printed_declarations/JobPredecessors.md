# `JobPredecessors`

- Kind (Rocq): Class
- Rocq: `prosa.results.transfer_schedulability.paper_model.JobPredecessors`
- Lean: `Prosa.Results.TransferSchedulability.PaperModel.JobPredecessors`
- Certificate: `JobPredecessors_source_total, JobPredecessors_target_total`

## Official Rocq

```coq
JobPredecessors : JobType -> Type

JobPredecessors is not universe polymorphic
Arguments JobPredecessors Job
Expands to: Inductive prosa.results.transfer_schedulability.paper_model.JobPredecessors
Declared in library prosa.results.transfer_schedulability.paper_model, line 42, characters 6-21
JobPredecessors
     : JobType -> Type
```

Body:

```coq
Record JobPredecessors (Job : JobType) : Type := Build_JobPredecessors
  { job_predecessors : Equality.sort Job -> seq (Equality.sort Job) }.

Arguments JobPredecessors Job
Arguments Build_JobPredecessors Job job_predecessors%function_scope
Arguments job_predecessors {Job JobPredecessors} _
```

## Lean

```lean
Prosa.Results.TransferSchedulability.PaperModel.JobPredecessors : (Job : Prosa.Behavior.Job.JobType) →
  [DecidableEq Job] → Type u_1
```

Body:

```lean
class Prosa.Results.TransferSchedulability.PaperModel.JobPredecessors.{u_1} (Job : Prosa.Behavior.Job.JobType)
  [DecidableEq Job] : Type u_1
number of parameters: 2
fields:
  Prosa.Results.TransferSchedulability.PaperModel.JobPredecessors.job_predecessors : Job → List Job
constructor:
  Prosa.Results.TransferSchedulability.PaperModel.JobPredecessors.mk.{u_1} {Job : Prosa.Behavior.Job.JobType}
    [DecidableEq Job] (job_predecessors : Job → List Job) :
    Prosa.Results.TransferSchedulability.PaperModel.JobPredecessors Job
```

## Lean, imported into Rocq

```coq
Prosa_Results_TransferSchedulability_PaperModel_JobPredecessors
     : forall Job : Prosa_Behavior_Job_JobType, DecidableEq Job -> Type
```

Body:

```coq
Record
Prosa_Results_TransferSchedulability_PaperModel_JobPredecessors@{u_1 Lean.u_1+1.0 Lean.u_1+2.0}
    (Job : Prosa_Behavior_Job_JobType)
(inst_3 : DecidableEq Job)
  : Type := Prosa_Results_TransferSchedulability_PaperModel_JobPredecessors_mk
  { job_predecessors : Job -> List Job } as default_proj_id.

Prosa_Results_TransferSchedulability_PaperModel_JobPredecessors has primitive projections with eta conversion.
Arguments Prosa_Results_TransferSchedulability_PaperModel_JobPredecessors Job
  inst_3
Arguments Prosa_Results_TransferSchedulability_PaperModel_JobPredecessors_mk Job
  inst_3 job_predecessors%_function_scope
```
