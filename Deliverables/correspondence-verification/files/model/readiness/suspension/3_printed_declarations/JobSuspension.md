# `JobSuspension`

- Kind (Rocq): Class
- Rocq: `prosa.model.readiness.suspension.JobSuspension`
- Lean: `Prosa.Model.Readiness.Suspension.JobSuspension`
- Certificate: `JobSuspension_source_total, JobSuspension_target_total`

## Official Rocq

```coq
JobSuspension : JobType -> Type

JobSuspension is not universe polymorphic
Arguments JobSuspension Job
JobSuspension is transparent
Expands to: Constant prosa.model.readiness.suspension.JobSuspension
Declared in library prosa.model.readiness.suspension, line 14, characters 0-80
JobSuspension
     : JobType -> Type
```

Body:

```coq
JobSuspension = fun Job : JobType => Equality.sort Job -> work -> duration
     : JobType -> Type

Arguments JobSuspension Job
```

## Lean

```lean
Prosa.Model.Readiness.Suspension.JobSuspension : (Job : Prosa.Behavior.Job.JobType) → [DecidableEq Job] → Type u_1
```

Body:

```lean
class Prosa.Model.Readiness.Suspension.JobSuspension.{u_1} (Job : Prosa.Behavior.Job.JobType) [DecidableEq Job] :
  Type u_1
number of parameters: 2
fields:
  Prosa.Model.Readiness.Suspension.JobSuspension.job_suspension : Job →
      Prosa.Behavior.Job.work → Prosa.Behavior.Time.duration
constructor:
  Prosa.Model.Readiness.Suspension.JobSuspension.mk.{u_1} {Job : Prosa.Behavior.Job.JobType} [DecidableEq Job]
    (job_suspension : Job → Prosa.Behavior.Job.work → Prosa.Behavior.Time.duration) :
    Prosa.Model.Readiness.Suspension.JobSuspension Job
```

## Lean, imported into Rocq

```coq
Prosa_Model_Readiness_Suspension_JobSuspension
     : forall Job : Prosa_Behavior_Job_JobType, DecidableEq Job -> Type
```

Body:

```coq
Record
Prosa_Model_Readiness_Suspension_JobSuspension@{u_1 Lean.u_1+1.0 Lean.u_1+2.0}
    (Job : Prosa_Behavior_Job_JobType)
(inst_3 : DecidableEq Job)
  : Type := Prosa_Model_Readiness_Suspension_JobSuspension_mk
  { job_suspension : Job -> Prosa_Behavior_Job_work -> Prosa_Behavior_Time_duration } as default_proj_id.

Prosa_Model_Readiness_Suspension_JobSuspension has primitive projections with eta conversion.
Arguments Prosa_Model_Readiness_Suspension_JobSuspension Job
  inst_3
Arguments Prosa_Model_Readiness_Suspension_JobSuspension_mk Job
  inst_3 job_suspension%_function_scope
```
