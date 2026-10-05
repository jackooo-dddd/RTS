# `job_cost_in_nonpreemptive_points`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.preemption.job.limited.job_cost_in_nonpreemptive_points`
- Lean: `Prosa.Analysis.Facts.Preemption.Job.Limited.job_cost_in_nonpreemptive_points`
- Certificate: `job_cost_in_nonpreemptive_points_correspondence`

## Official Rocq

```coq
job_cost_in_nonpreemptive_points :
forall {Job : JobType} {H2 : JobCost Job} {H3 : JobPreemptionPoints Job} (arr_seq : arrival_sequence Job),
@valid_limited_preemptions_job_model Job H2 H3 arr_seq ->
forall j : Equality.sort Job,
@arrives_in Job arr_seq j -> is_true (@job_cost Job H2 j \in @job_preemptive_points Job H3 j)

job_cost_in_nonpreemptive_points is not universe polymorphic
Arguments job_cost_in_nonpreemptive_points {Job H2 H3} arr_seq H_valid_limited_preemptions_job_model 
  j H_j_arrives
job_cost_in_nonpreemptive_points is opaque
Expands to: Constant prosa.analysis.facts.preemption.job.limited.job_cost_in_nonpreemptive_points
Declared in library prosa.analysis.facts.preemption.job.limited, line 79, characters 10-42
@job_cost_in_nonpreemptive_points
     : forall (Job : JobType) (H2 : JobCost Job) (H3 : JobPreemptionPoints Job)
         (arr_seq : arrival_sequence Job),
       @valid_limited_preemptions_job_model Job H2 H3 arr_seq ->
       forall j : Equality.sort Job,
       @arrives_in Job arr_seq j -> is_true (@job_cost Job H2 j \in @job_preemptive_points Job H3 j)
```

## Lean

```lean
@Prosa.Analysis.Facts.Preemption.Job.Limited.job_cost_in_nonpreemptive_points : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobCost Job]
  [inst_2 : Prosa.Model.Preemption.LimitedPreemptive.JobPreemptionPoints Job]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Model.Preemption.LimitedPreemptive.valid_limited_preemptions_job_model arr_seq →
    ∀ (j : Job),
      Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j →
        decide (Prosa.Behavior.Job.job_cost j ∈ Prosa.Model.Preemption.LimitedPreemptive.job_preemptive_points j) = true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Preemption_Job_Limited_job_cost_in_nonpreemptive_points
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (inst_6 : 
          Prosa_Behavior_Job_JobCost Job
            inst_3)
         (inst_9 : 
          Prosa_Model_Preemption_LimitedPreemptive_JobPreemptionPoints Job
            inst_3)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_3),
       Prosa_Model_Preemption_LimitedPreemptive_valid_limited_preemptions_job_model Job
         inst_3
         inst_6
         inst_9 arr_seq ->
       forall j : Job,
       Prosa_Behavior_Arrival_sequence_arrives_in Job
         inst_3 arr_seq j ->
       @eq Bool
         (Decidable_decide
            (Membership_mem_inst3 Prosa_Behavior_Job_work (List_inst1 Prosa_Behavior_Job_work)
               (List_instMembership_inst1 Prosa_Behavior_Job_work)
               (Prosa_Model_Preemption_LimitedPreemptive_JobPreemptionPoints_job_preemptive_points Job
                  inst_3
                  inst_9 j)
               (Prosa_Behavior_Job_JobCost_job_cost Job
                  inst_3
                  inst_6 j))
            (List_instDecidableMemOfLawfulBEq_inst1 Prosa_Behavior_Job_work
               (instBEqOfDecidableEq_inst1 Prosa_Behavior_Job_work instDecidableEqNat) Nat_instLawfulBEq
               (Prosa_Behavior_Job_JobCost_job_cost Job
                  inst_3
                  inst_6 j)
               (Prosa_Model_Preemption_LimitedPreemptive_JobPreemptionPoints_job_preemptive_points Job
                  inst_3
                  inst_9 j)))
         Bool_true
```
