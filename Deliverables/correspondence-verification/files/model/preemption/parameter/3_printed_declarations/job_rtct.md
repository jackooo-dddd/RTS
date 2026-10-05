# `job_rtct`

- Kind (Rocq): Definition
- Rocq: `prosa.model.preemption.parameter.job_rtct`
- Lean: `Prosa.Model.Preemption.Parameter.job_rtct`
- Certificate: `job_rtct_correspondence`

## Official Rocq

```coq
job_rtct : forall {Job : JobType}, JobCost Job -> JobPreemptable Job -> Equality.sort Job -> nat

job_rtct is not universe polymorphic
Arguments job_rtct {Job H0 H1} j
job_rtct is transparent
Expands to: Constant prosa.model.preemption.parameter.job_rtct
Declared in library prosa.model.preemption.parameter, line 62, characters 13-21
@job_rtct
     : forall Job : JobType, JobCost Job -> JobPreemptable Job -> Equality.sort Job -> nat
```

Body:

```coq
job_rtct =
fun (Job : JobType) (H0 : JobCost Job) (H1 : JobPreemptable Job) (j : Equality.sort Job) =>
@job_cost Job H0 j - (@job_last_nonpreemptive_segment Job H0 H1 j - 1)
     : forall {Job : JobType}, JobCost Job -> JobPreemptable Job -> Equality.sort Job -> nat

Arguments job_rtct {Job H0 H1} j
```

## Lean

```lean
@Prosa.Model.Preemption.Parameter.job_rtct : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [Prosa.Behavior.Job.JobCost Job] → [Prosa.Model.Preemption.Parameter.JobPreemptable Job] → Job → ℕ
```

Body:

```lean
def Prosa.Model.Preemption.Parameter.job_rtct.{u_1} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [Prosa.Behavior.Job.JobCost Job] → [Prosa.Model.Preemption.Parameter.JobPreemptable Job] → Job → ℕ :=
fun {Job} [DecidableEq Job] [Prosa.Behavior.Job.JobCost Job] [Prosa.Model.Preemption.Parameter.JobPreemptable Job] j =>
  Prosa.Behavior.Job.job_cost j - (Prosa.Model.Preemption.Parameter.job_last_nonpreemptive_segment j - 1)
```

## Lean, imported into Rocq

```coq
Prosa_Model_Preemption_Parameter_job_rtct
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Behavior_Job_JobCost Job inst_3 ->
       Prosa_Model_Preemption_Parameter_JobPreemptable Job
         inst_3 ->
       Job -> Nat
```

Body:

```coq
Prosa_Model_Preemption_Parameter_job_rtct@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (inst_6 : Prosa_Behavior_Job_JobCost Job
                                                                             inst_3)
  (inst_9 : Prosa_Model_Preemption_Parameter_JobPreemptable
                                                                             Job
                                                                             inst_3)
  (j : Job) =>
HSub_hSub_inst7 Prosa_Behavior_Job_work Nat Prosa_Behavior_Job_work
  (instHSub_inst1 Prosa_Behavior_Job_work instSubNat)
  (Prosa_Behavior_Job_JobCost_job_cost Job
     inst_3
     inst_6 j)
  (HSub_hSub_inst7 Nat Nat Nat (instHSub_inst1 Nat instSubNat)
     (Prosa_Model_Preemption_Parameter_job_last_nonpreemptive_segment Job
        inst_3
        inst_6
        inst_9 j)
     (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1)))
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Behavior_Job_JobCost Job inst_3 ->
       Prosa_Model_Preemption_Parameter_JobPreemptable Job
         inst_3 ->
       Job -> Nat

Arguments Prosa_Model_Preemption_Parameter_job_rtct Job
  inst_3
  inst_6
  inst_9 j
```
