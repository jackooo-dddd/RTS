# `JobPreemptionPoints`

- Kind (Rocq): Class
- Rocq: `prosa.model.preemption.limited_preemptive.JobPreemptionPoints`
- Lean: `Prosa.Model.Preemption.LimitedPreemptive.JobPreemptionPoints`
- Certificate: `JobPreemptionPoints_source_total, JobPreemptionPoints_target_total`

## Official Rocq

```coq
JobPreemptionPoints : JobType -> Type

JobPreemptionPoints is not universe polymorphic
Arguments JobPreemptionPoints Job
Expands to: Inductive prosa.model.preemption.limited_preemptive.JobPreemptionPoints
Declared in library prosa.model.preemption.limited_preemptive, line 14, characters 6-25
JobPreemptionPoints
     : JobType -> Type
```

Body:

```coq
Record JobPreemptionPoints (Job : JobType) : Type := Build_JobPreemptionPoints
  { job_preemptive_points : Equality.sort Job -> seq work }.

Arguments JobPreemptionPoints Job
Arguments Build_JobPreemptionPoints Job job_preemptive_points%function_scope
Arguments job_preemptive_points {Job JobPreemptionPoints} _
```

## Lean

```lean
Prosa.Model.Preemption.LimitedPreemptive.JobPreemptionPoints : (Job : Prosa.Behavior.Job.JobType) →
  [DecidableEq Job] → Type u_1
```

Body:

```lean
class Prosa.Model.Preemption.LimitedPreemptive.JobPreemptionPoints.{u_1} (Job : Prosa.Behavior.Job.JobType)
  [DecidableEq Job] : Type u_1
number of parameters: 2
fields:
  Prosa.Model.Preemption.LimitedPreemptive.JobPreemptionPoints.job_preemptive_points : Job →
      List Prosa.Behavior.Job.work
constructor:
  Prosa.Model.Preemption.LimitedPreemptive.JobPreemptionPoints.mk.{u_1} {Job : Prosa.Behavior.Job.JobType}
    [DecidableEq Job] (job_preemptive_points : Job → List Prosa.Behavior.Job.work) :
    Prosa.Model.Preemption.LimitedPreemptive.JobPreemptionPoints Job
```

## Lean, imported into Rocq

```coq
Prosa_Model_Preemption_LimitedPreemptive_JobPreemptionPoints
     : forall Job : Prosa_Behavior_Job_JobType, DecidableEq Job -> Type
```

Body:

```coq
Record
Prosa_Model_Preemption_LimitedPreemptive_JobPreemptionPoints@{u_1 Lean.u_1+1.0 Lean.u_1+2.0}
    (Job : Prosa_Behavior_Job_JobType)
(inst_3 : DecidableEq Job)
  : Type := Prosa_Model_Preemption_LimitedPreemptive_JobPreemptionPoints_mk
  { job_preemptive_points : Job -> List_inst1 Prosa_Behavior_Job_work } as default_proj_id.

Prosa_Model_Preemption_LimitedPreemptive_JobPreemptionPoints has primitive projections with eta conversion.
Arguments Prosa_Model_Preemption_LimitedPreemptive_JobPreemptionPoints Job
  inst_3
Arguments Prosa_Model_Preemption_LimitedPreemptive_JobPreemptionPoints_mk Job
  inst_3
  job_preemptive_points%_function_scope
```
