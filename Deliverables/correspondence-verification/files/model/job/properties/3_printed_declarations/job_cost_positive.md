# `job_cost_positive`

- Kind (Rocq): Definition
- Rocq: `prosa.model.job.properties.job_cost_positive`
- Lean: `Prosa.Model.Job.Properties.job_cost_positive`
- Certificate: `job_cost_positive_correspondence`

## Official Rocq

```coq
job_cost_positive : forall {Job : JobType}, JobCost Job -> Equality.sort Job -> bool

job_cost_positive is not universe polymorphic
Arguments job_cost_positive {Job H} j
job_cost_positive is transparent
Expands to: Constant prosa.model.job.properties.job_cost_positive
Declared in library prosa.model.job.properties, line 14, characters 13-30
@job_cost_positive
     : forall Job : JobType, JobCost Job -> Equality.sort Job -> bool
```

Body:

```coq
job_cost_positive =
fun (Job : JobType) (H : JobCost Job) (j : Equality.sort Job) => 0 < @job_cost Job H j
     : forall {Job : JobType}, JobCost Job -> Equality.sort Job -> bool

Arguments job_cost_positive {Job H} j
```

## Lean

```lean
@Prosa.Model.Job.Properties.job_cost_positive : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] → [Prosa.Behavior.Job.JobCost Job] → Job → Bool
def Prosa.Model.Job.Properties.job_cost_positive.{u_1} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] → [Prosa.Behavior.Job.JobCost Job] → Job → Bool :=
fun {Job} [DecidableEq Job] [Prosa.Behavior.Job.JobCost Job] j => decide (Prosa.Behavior.Job.job_cost j > 0)
```

## Lean, imported into Rocq

```coq
Prosa_Model_Job_Properties_job_cost_positive
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Behavior_Job_JobCost Job inst_3 ->
       Job -> Bool
```

Body:

```coq
Prosa_Model_Job_Properties_job_cost_positive@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (inst_6 : Prosa_Behavior_Job_JobCost Job
                                                                      inst_3)
  (j : Job) =>
Decidable_decide
  (GT_gt_inst1 Prosa_Behavior_Job_work instLTNat
     (Prosa_Behavior_Job_JobCost_job_cost Job inst_3
        inst_6 j)
     (OfNat_ofNat_inst1 Prosa_Behavior_Job_work 0 (instOfNatNat 0)))
  (Nat_decLt (OfNat_ofNat_inst1 Prosa_Behavior_Job_work 0 (instOfNatNat 0))
     (Prosa_Behavior_Job_JobCost_job_cost Job inst_3
        inst_6 j))
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Behavior_Job_JobCost Job inst_3 ->
       Job -> Bool

Arguments Prosa_Model_Job_Properties_job_cost_positive Job
  inst_3
  inst_6 j
```
