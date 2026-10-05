# `number_of_preemption_points_at_least_two`

- Kind (Rocq): Corollary
- Rocq: `prosa.analysis.facts.preemption.job.limited.number_of_preemption_points_at_least_two`
- Lean: `Prosa.Analysis.Facts.Preemption.Job.Limited.number_of_preemption_points_at_least_two`
- Certificate: `number_of_preemption_points_at_least_two_correspondence`

## Official Rocq

```coq
number_of_preemption_points_at_least_two :
forall {Job : JobType} {H2 : JobCost Job} {H3 : JobPreemptionPoints Job} (arr_seq : arrival_sequence Job),
@valid_limited_preemptions_job_model Job H2 H3 arr_seq ->
forall j : Equality.sort Job,
@arrives_in Job arr_seq j ->
is_true (@job_cost_positive Job H2 j) -> is_true (1 < @size work (@job_preemptive_points Job H3 j))

number_of_preemption_points_at_least_two is not universe polymorphic
Arguments number_of_preemption_points_at_least_two {Job H2 H3} arr_seq H_valid_limited_preemptions_job_model
  j H_j_arrives _
number_of_preemption_points_at_least_two is opaque
Expands to: Constant prosa.analysis.facts.preemption.job.limited.number_of_preemption_points_at_least_two
Declared in library prosa.analysis.facts.preemption.job.limited, line 94, characters 14-54
@number_of_preemption_points_at_least_two
     : forall (Job : JobType) (H2 : JobCost Job) (H3 : JobPreemptionPoints Job)
         (arr_seq : arrival_sequence Job),
       @valid_limited_preemptions_job_model Job H2 H3 arr_seq ->
       forall j : Equality.sort Job,
       @arrives_in Job arr_seq j ->
       is_true (@job_cost_positive Job H2 j) -> is_true (1 < @size work (@job_preemptive_points Job H3 j))
```

## Lean

```lean
@Prosa.Analysis.Facts.Preemption.Job.Limited.number_of_preemption_points_at_least_two : ∀
  {Job : Prosa.Behavior.Job.JobType} [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobCost Job]
  [inst_2 : Prosa.Model.Preemption.LimitedPreemptive.JobPreemptionPoints Job]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Model.Preemption.LimitedPreemptive.valid_limited_preemptions_job_model arr_seq →
    ∀ (j : Job),
      Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j →
        Prosa.Model.Job.Properties.job_cost_positive j = true →
          1 < (Prosa.Model.Preemption.LimitedPreemptive.job_preemptive_points j).length
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Preemption_Job_Limited_number_of_preemption_points_at_least_two
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
         (Prosa_Model_Job_Properties_job_cost_positive Job
            inst_3
            inst_6 j)
         Bool_true ->
       LT_lt_inst1 Nat instLTNat (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1))
         (List_length_inst1 Prosa_Behavior_Job_work
            (Prosa_Model_Preemption_LimitedPreemptive_JobPreemptionPoints_job_preemptive_points Job
               inst_3
               inst_9 j))
```
