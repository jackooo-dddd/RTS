# `ref_cost_bounds_online_cost`

- Kind (Rocq): Corollary
- Rocq: `prosa.results.transfer_schedulability.criterion.ref_cost_bounds_online_cost`
- Lean: `Prosa.Results.TransferSchedulability.Criterion.ref_cost_bounds_online_cost`
- Certificate: `ref_cost_bounds_online_cost_correspondence`

## Official Rocq

```coq
ref_cost_bounds_online_cost :
forall {Job : JobType} (ref_job_cost online_job_cost job_cost_bound : JobCost Job),
(forall j : Equality.sort Job, is_true (online_job_cost j <= job_cost_bound j)) ->
(forall j : Equality.sort Job, is_true (job_cost_bound j <= ref_job_cost j)) ->
forall j : Equality.sort Job, is_true (online_job_cost j <= ref_job_cost j)

ref_cost_bounds_online_cost is not universe polymorphic
Arguments ref_cost_bounds_online_cost {Job} ref_job_cost online_job_cost job_cost_bound
  (H_job_cost_bounded H_ref_cost_dominates)%function_scope j
ref_cost_bounds_online_cost is opaque
Expands to: Constant prosa.results.transfer_schedulability.criterion.ref_cost_bounds_online_cost
Declared in library prosa.results.transfer_schedulability.criterion, line 188, characters 14-41
@ref_cost_bounds_online_cost
     : forall (Job : JobType) (ref_job_cost online_job_cost job_cost_bound : JobCost Job),
       (forall j : Equality.sort Job, is_true (online_job_cost j <= job_cost_bound j)) ->
       (forall j : Equality.sort Job, is_true (job_cost_bound j <= ref_job_cost j)) ->
       forall j : Equality.sort Job, is_true (online_job_cost j <= ref_job_cost j)
```

## Lean

```lean
@Prosa.Results.TransferSchedulability.Criterion.ref_cost_bounds_online_cost : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] (ref_job_cost online_job_cost job_cost_bound : Prosa.Behavior.Job.JobCost Job),
  (∀ (j : Job), Prosa.Behavior.Job.job_cost j ≤ Prosa.Behavior.Job.job_cost j) →
    (∀ (j : Job), Prosa.Behavior.Job.job_cost j ≤ Prosa.Behavior.Job.job_cost j) →
      ∀ (j : Job), Prosa.Behavior.Job.job_cost j ≤ Prosa.Behavior.Job.job_cost j
```

## Lean, imported into Rocq

```coq
Prosa_Results_TransferSchedulability_Criterion_ref_cost_bounds_online_cost
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : 
          DecidableEq Job)
         (ref_job_cost online_job_cost
          job_cost_bound : Prosa_Behavior_Job_JobCost Job
                             inst_3),
       (forall j : Job,
        LE_le_inst1 Prosa_Behavior_Job_work instLENat
          (Prosa_Behavior_Job_JobCost_job_cost Job
             inst_3
             online_job_cost j)
          (Prosa_Behavior_Job_JobCost_job_cost Job
             inst_3
             job_cost_bound j)) ->
       (forall j : Job,
        LE_le_inst1 Prosa_Behavior_Job_work instLENat
          (Prosa_Behavior_Job_JobCost_job_cost Job
             inst_3
             job_cost_bound j)
          (Prosa_Behavior_Job_JobCost_job_cost Job
             inst_3 ref_job_cost
             j)) ->
       forall j : Job,
       LE_le_inst1 Prosa_Behavior_Job_work instLENat
         (Prosa_Behavior_Job_JobCost_job_cost Job
            inst_3
            online_job_cost j)
         (Prosa_Behavior_Job_JobCost_job_cost Job
            inst_3 ref_job_cost
            j)
```
