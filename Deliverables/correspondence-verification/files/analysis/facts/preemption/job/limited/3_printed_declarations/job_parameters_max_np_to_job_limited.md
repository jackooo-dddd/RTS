# `job_parameters_max_np_to_job_limited`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.preemption.job.limited.job_parameters_max_np_to_job_limited`
- Lean: `Prosa.Analysis.Facts.Preemption.Job.Limited.job_parameters_max_np_to_job_limited`
- Certificate: `job_parameters_max_np_to_job_limited_correspondence`

## Official Rocq

```coq
job_parameters_max_np_to_job_limited :
forall {Job : JobType} {H2 : JobCost Job} {H3 : JobPreemptionPoints Job} (arr_seq : arrival_sequence Job),
@valid_limited_preemptions_job_model Job H2 H3 arr_seq ->
forall j : Equality.sort Job,
@arrives_in Job arr_seq j ->
max0 (distances (@job_preemption_points Job H2 (@limited_preemptive_job_model Job H3) j)) =
max0 (distances (@job_preemptive_points Job H3 j))

job_parameters_max_np_to_job_limited is not universe polymorphic
Arguments job_parameters_max_np_to_job_limited {Job H2 H3} arr_seq H_valid_limited_preemptions_job_model 
  j H_j_arrives
job_parameters_max_np_to_job_limited is opaque
Expands to: Constant prosa.analysis.facts.preemption.job.limited.job_parameters_max_np_to_job_limited
Declared in library prosa.analysis.facts.preemption.job.limited, line 184, characters 10-46
@job_parameters_max_np_to_job_limited
     : forall (Job : JobType) (H2 : JobCost Job) (H3 : JobPreemptionPoints Job)
         (arr_seq : arrival_sequence Job),
       @valid_limited_preemptions_job_model Job H2 H3 arr_seq ->
       forall j : Equality.sort Job,
       @arrives_in Job arr_seq j ->
       max0 (distances (@job_preemption_points Job H2 (@limited_preemptive_job_model Job H3) j)) =
       max0 (distances (@job_preemptive_points Job H3 j))
```

## Lean

```lean
@Prosa.Analysis.Facts.Preemption.Job.Limited.job_parameters_max_np_to_job_limited : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobCost Job]
  [inst_2 : Prosa.Model.Preemption.LimitedPreemptive.JobPreemptionPoints Job]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Model.Preemption.LimitedPreemptive.valid_limited_preemptions_job_model arr_seq →
    ∀ (j : Job),
      Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j →
        Prosa.Util.List.max0
            (Prosa.Util.Nondecreasing.distances (Prosa.Model.Preemption.Parameter.job_preemption_points j)) =
          Prosa.Util.List.max0
            (Prosa.Util.Nondecreasing.distances (Prosa.Model.Preemption.LimitedPreemptive.job_preemptive_points j))
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Preemption_Job_Limited_job_parameters_max_np_to_job_limited
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
       @eq Nat
         (Prosa_Util_List_max0
            (Prosa_Util_Nondecreasing_distances
               (Prosa_Model_Preemption_Parameter_job_preemption_points Job
                  inst_3
                  inst_6
                  (Prosa_Model_Preemption_LimitedPreemptive_limited_preemptive_job_model Job
                     inst_3
                     inst_9)
                  j)))
         (Prosa_Util_List_max0
            (Prosa_Util_Nondecreasing_distances
               (Prosa_Model_Preemption_LimitedPreemptive_JobPreemptionPoints_job_preemptive_points Job
                  inst_3
                  inst_9 j)))
```
