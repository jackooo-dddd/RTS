# `job_max_nps_is_ε`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.preemption.job.preemptive.job_max_nps_is_ε`
- Lean: `Prosa.Analysis.Facts.Preemption.Job.Preemptive.job_max_nps_is_ε`
- Certificate: `job_max_nps_is_ε_correspondence`

## Official Rocq

```coq
job_max_nps_is_ε :
forall {Job : JobType} {H0 : JobCost Job} (j : Equality.sort Job),
is_true (0 < @job_cost Job H0 j) ->
@job_max_nonpreemptive_segment Job H0 (@fully_preemptive_job_model Job) j = 1

job_max_nps_is_ε is not universe polymorphic
Arguments job_max_nps_is_ε {Job H0} j _
job_max_nps_is_ε is opaque
Expands to: Constant prosa.analysis.facts.preemption.job.preemptive.job_max_nps_is_ε
Declared in library prosa.analysis.facts.preemption.job.preemptive, line 49, characters 8-25
@job_max_nps_is_ε
     : forall (Job : JobType) (H0 : JobCost Job) (j : Equality.sort Job),
       is_true (0 < @job_cost Job H0 j) ->
       @job_max_nonpreemptive_segment Job H0 (@fully_preemptive_job_model Job) j = 1
```

## Lean

```lean
@Prosa.Analysis.Facts.Preemption.Job.Preemptive.job_max_nps_is_ε : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobCost Job] (j : Job),
  0 < Prosa.Behavior.Job.job_cost j → Prosa.Model.Preemption.Parameter.job_max_nonpreemptive_segment j = 1
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Preemption_Job_Preemptive_job_max_nps_is__UU03b5_
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : 
          DecidableEq Job)
         (inst_6 : 
          Prosa_Behavior_Job_JobCost Job
            inst_3)
         (j : Job),
       LT_lt_inst1 Prosa_Behavior_Job_work instLTNat
         (OfNat_ofNat_inst1 Prosa_Behavior_Job_work 0 (instOfNatNat 0))
         (Prosa_Behavior_Job_JobCost_job_cost Job
            inst_3
            inst_6 j) ->
       @eq Nat
         (Prosa_Model_Preemption_Parameter_job_max_nonpreemptive_segment Job
            inst_3
            inst_6
            (Prosa_Model_Preemption_FullyPreemptive_fully_preemptive_job_model Job
               inst_3)
            j)
         (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1))
```
