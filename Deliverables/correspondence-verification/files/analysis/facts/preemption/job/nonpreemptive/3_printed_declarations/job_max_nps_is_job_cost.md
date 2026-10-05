# `job_max_nps_is_job_cost`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.preemption.job.nonpreemptive.job_max_nps_is_job_cost`
- Lean: `Prosa.Analysis.Facts.Preemption.Job.Nonpreemptive.job_max_nps_is_job_cost`
- Certificate: `job_max_nps_is_job_cost_correspondence`

## Official Rocq

```coq
job_max_nps_is_job_cost :
forall {Job : JobType} {H0 : JobCost Job} (j : Equality.sort Job),
@job_max_nonpreemptive_segment Job H0 (@fully_nonpreemptive_job_model Job H0) j = @job_cost Job H0 j

job_max_nps_is_job_cost is not universe polymorphic
Arguments job_max_nps_is_job_cost {Job H0} j
job_max_nps_is_job_cost is opaque
Expands to: Constant prosa.analysis.facts.preemption.job.nonpreemptive.job_max_nps_is_job_cost
Declared in library prosa.analysis.facts.preemption.job.nonpreemptive, line 67, characters 8-31
@job_max_nps_is_job_cost
     : forall (Job : JobType) (H0 : JobCost Job) (j : Equality.sort Job),
       @job_max_nonpreemptive_segment Job H0 (@fully_nonpreemptive_job_model Job H0) j = @job_cost Job H0 j
```

## Lean

```lean
@Prosa.Analysis.Facts.Preemption.Job.Nonpreemptive.job_max_nps_is_job_cost : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobCost Job] (j : Job),
  Prosa.Model.Preemption.Parameter.job_max_nonpreemptive_segment j = Prosa.Behavior.Job.job_cost j
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Preemption_Job_Nonpreemptive_job_max_nps_is_job_cost
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : 
          DecidableEq Job)
         (inst_6 : 
          Prosa_Behavior_Job_JobCost Job
            inst_3)
         (j : Job),
       @eq Nat
         (Prosa_Model_Preemption_Parameter_job_max_nonpreemptive_segment Job
            inst_3
            inst_6
            (Prosa_Model_Preemption_FullyNonpreemptive_fully_nonpreemptive_job_model Job
               inst_3
               inst_6)
            j)
         (Prosa_Behavior_Job_JobCost_job_cost Job
            inst_3
            inst_6 j)
```
