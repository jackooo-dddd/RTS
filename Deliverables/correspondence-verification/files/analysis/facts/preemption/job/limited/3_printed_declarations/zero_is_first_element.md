# `zero_is_first_element`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.preemption.job.limited.zero_is_first_element`
- Lean: `Prosa.Analysis.Facts.Preemption.Job.Limited.zero_is_first_element`
- Certificate: `zero_is_first_element_correspondence`

## Official Rocq

```coq
zero_is_first_element :
forall {Job : JobType} {H2 : JobCost Job} {H3 : JobPreemptionPoints Job} (arr_seq : arrival_sequence Job),
@valid_limited_preemptions_job_model Job H2 H3 arr_seq ->
forall j : Equality.sort Job, @arrives_in Job arr_seq j -> first0 (@job_preemptive_points Job H3 j) = 0

zero_is_first_element is not universe polymorphic
Arguments zero_is_first_element {Job H2 H3} arr_seq H_valid_limited_preemptions_job_model j H_j_arrives
zero_is_first_element is opaque
Expands to: Constant prosa.analysis.facts.preemption.job.limited.zero_is_first_element
Declared in library prosa.analysis.facts.preemption.job.limited, line 61, characters 10-31
@zero_is_first_element
     : forall (Job : JobType) (H2 : JobCost Job) (H3 : JobPreemptionPoints Job)
         (arr_seq : arrival_sequence Job),
       @valid_limited_preemptions_job_model Job H2 H3 arr_seq ->
       forall j : Equality.sort Job,
       @arrives_in Job arr_seq j -> first0 (@job_preemptive_points Job H3 j) = 0
```

## Lean

```lean
@Prosa.Analysis.Facts.Preemption.Job.Limited.zero_is_first_element : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobCost Job]
  [inst_2 : Prosa.Model.Preemption.LimitedPreemptive.JobPreemptionPoints Job]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Model.Preemption.LimitedPreemptive.valid_limited_preemptions_job_model arr_seq →
    ∀ (j : Job),
      Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j →
        Prosa.Util.List.first0 (Prosa.Model.Preemption.LimitedPreemptive.job_preemptive_points j) = 0
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Preemption_Job_Limited_zero_is_first_element
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
         (Prosa_Util_List_first0
            (Prosa_Model_Preemption_LimitedPreemptive_JobPreemptionPoints_job_preemptive_points Job
               inst_3
               inst_9 j))
         (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0))
```
