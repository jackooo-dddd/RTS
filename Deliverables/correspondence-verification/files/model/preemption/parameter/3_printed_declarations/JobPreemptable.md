# `JobPreemptable`

- Kind (Rocq): Class
- Rocq: `prosa.model.preemption.parameter.JobPreemptable`
- Lean: `Prosa.Model.Preemption.Parameter.JobPreemptable`
- Certificate: `JobPreemptable_source_total, JobPreemptable_target_total`

## Official Rocq

```coq
JobPreemptable : JobType -> Type

JobPreemptable is not universe polymorphic
Arguments JobPreemptable Job
JobPreemptable is transparent
Expands to: Constant prosa.model.preemption.parameter.JobPreemptable
Declared in library prosa.model.preemption.parameter, line 12, characters 0-80
JobPreemptable
     : JobType -> Type
```

Body:

```coq
JobPreemptable = fun Job : JobType => Equality.sort Job -> work -> bool
     : JobType -> Type

Arguments JobPreemptable Job
```

## Lean

```lean
Prosa.Model.Preemption.Parameter.JobPreemptable : (Job : Prosa.Behavior.Job.JobType) → [DecidableEq Job] → Type u_1
```

Body:

```lean
class Prosa.Model.Preemption.Parameter.JobPreemptable.{u_1} (Job : Prosa.Behavior.Job.JobType) [DecidableEq Job] :
  Type u_1
number of parameters: 2
fields:
  Prosa.Model.Preemption.Parameter.JobPreemptable.job_preemptable : Job → Prosa.Behavior.Job.work → Bool
constructor:
  Prosa.Model.Preemption.Parameter.JobPreemptable.mk.{u_1} {Job : Prosa.Behavior.Job.JobType} [DecidableEq Job]
    (job_preemptable : Job → Prosa.Behavior.Job.work → Bool) : Prosa.Model.Preemption.Parameter.JobPreemptable Job
```

## Lean, imported into Rocq

```coq
Prosa_Model_Preemption_Parameter_JobPreemptable
     : forall Job : Prosa_Behavior_Job_JobType, DecidableEq Job -> Type
```

Body:

```coq
Record
Prosa_Model_Preemption_Parameter_JobPreemptable@{u_1 Lean.u_1+1.0 Lean.u_1+2.0}
    (Job : Prosa_Behavior_Job_JobType)
(inst_3 : DecidableEq Job)
  : Type := Prosa_Model_Preemption_Parameter_JobPreemptable_mk
  { job_preemptable : Job -> Prosa_Behavior_Job_work -> Bool } as default_proj_id.

Prosa_Model_Preemption_Parameter_JobPreemptable has primitive projections with eta conversion.
Arguments Prosa_Model_Preemption_Parameter_JobPreemptable Job
  inst_3
Arguments Prosa_Model_Preemption_Parameter_JobPreemptable_mk Job
  inst_3 job_preemptable%_function_scope
```
