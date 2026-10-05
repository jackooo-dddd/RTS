# `list_of_preemption_point_is_not_empty`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.preemption.job.limited.list_of_preemption_point_is_not_empty`
- Lean: `Prosa.Analysis.Facts.Preemption.Job.Limited.list_of_preemption_point_is_not_empty`
- Certificate: `list_of_preemption_point_is_not_empty_correspondence`

## Official Rocq

```coq
list_of_preemption_point_is_not_empty :
forall {Job : JobType} {H2 : JobCost Job} {H3 : JobPreemptionPoints Job} (arr_seq : arrival_sequence Job),
@valid_limited_preemptions_job_model Job H2 H3 arr_seq ->
forall j : Equality.sort Job,
@arrives_in Job arr_seq j -> is_true (0 < @size work (@job_preemptive_points Job H3 j))

list_of_preemption_point_is_not_empty is not universe polymorphic
Arguments list_of_preemption_point_is_not_empty {Job H2 H3} arr_seq H_valid_limited_preemptions_job_model 
  j H_j_arrives
list_of_preemption_point_is_not_empty is opaque
Expands to: Constant prosa.analysis.facts.preemption.job.limited.list_of_preemption_point_is_not_empty
Declared in library prosa.analysis.facts.preemption.job.limited, line 69, characters 10-47
@list_of_preemption_point_is_not_empty
     : forall (Job : JobType) (H2 : JobCost Job) (H3 : JobPreemptionPoints Job)
         (arr_seq : arrival_sequence Job),
       @valid_limited_preemptions_job_model Job H2 H3 arr_seq ->
       forall j : Equality.sort Job,
       @arrives_in Job arr_seq j -> is_true (0 < @size work (@job_preemptive_points Job H3 j))
```

## Lean

```lean
@Prosa.Analysis.Facts.Preemption.Job.Limited.list_of_preemption_point_is_not_empty : ∀
  {Job : Prosa.Behavior.Job.JobType} [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobCost Job]
  [inst_2 : Prosa.Model.Preemption.LimitedPreemptive.JobPreemptionPoints Job]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Model.Preemption.LimitedPreemptive.valid_limited_preemptions_job_model arr_seq →
    ∀ (j : Job),
      Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j →
        0 < (Prosa.Model.Preemption.LimitedPreemptive.job_preemptive_points j).length
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Preemption_Job_Limited_list_of_preemption_point_is_not_empty
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
       LT_lt_inst1 Nat instLTNat (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0))
         (List_length_inst1 Prosa_Behavior_Job_work
            (Prosa_Model_Preemption_LimitedPreemptive_JobPreemptionPoints_job_preemptive_points Job
               inst_3
               inst_9 j))
```
