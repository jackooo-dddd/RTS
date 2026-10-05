# `job_max_nps_is_0`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.preemption.job.preemptive.job_max_nps_is_0`
- Lean: `Prosa.Analysis.Facts.Preemption.Job.Preemptive.job_max_nps_is_0`
- Certificate: `job_max_nps_is_0_correspondence`

## Official Rocq

```coq
job_max_nps_is_0 :
forall {Job : JobType} {H0 : JobCost Job} (j : Equality.sort Job),
@job_cost Job H0 j = 0 -> @job_max_nonpreemptive_segment Job H0 (@fully_preemptive_job_model Job) j = 0

job_max_nps_is_0 is not universe polymorphic
Arguments job_max_nps_is_0 {Job H0} j _
job_max_nps_is_0 is opaque
Expands to: Constant prosa.analysis.facts.preemption.job.preemptive.job_max_nps_is_0
Declared in library prosa.analysis.facts.preemption.job.preemptive, line 37, characters 8-24
@job_max_nps_is_0
     : forall (Job : JobType) (H0 : JobCost Job) (j : Equality.sort Job),
       @job_cost Job H0 j = 0 ->
       @job_max_nonpreemptive_segment Job H0 (@fully_preemptive_job_model Job) j = 0
```

## Lean

```lean
@Prosa.Analysis.Facts.Preemption.Job.Preemptive.job_max_nps_is_0 : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobCost Job] (j : Job),
  Prosa.Behavior.Job.job_cost j = 0 → Prosa.Model.Preemption.Parameter.job_max_nonpreemptive_segment j = 0
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Preemption_Job_Preemptive_job_max_nps_is_0
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : 
          DecidableEq Job)
         (inst_6 : 
          Prosa_Behavior_Job_JobCost Job
            inst_3)
         (j : Job),
       @eq Prosa_Behavior_Job_work
         (Prosa_Behavior_Job_JobCost_job_cost Job
            inst_3
            inst_6 j)
         (OfNat_ofNat_inst1 Prosa_Behavior_Job_work 0 (instOfNatNat 0)) ->
       @eq Nat
         (Prosa_Model_Preemption_Parameter_job_max_nonpreemptive_segment Job
            inst_3
            inst_6
            (Prosa_Model_Preemption_FullyPreemptive_fully_preemptive_job_model Job
               inst_3)
            j)
         (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0))
```
