# `antidensity_of_preemption_points`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.preemption.job.limited.antidensity_of_preemption_points`
- Lean: `Prosa.Analysis.Facts.Preemption.Job.Limited.antidensity_of_preemption_points`
- Certificate: `antidensity_of_preemption_points_correspondence`

## Official Rocq

```coq
antidensity_of_preemption_points :
forall {Job : JobType} {H2 : JobCost Job} {H3 : JobPreemptionPoints Job} (arr_seq : arrival_sequence Job),
@valid_limited_preemptions_job_model Job H2 H3 arr_seq ->
forall j : Equality.sort Job,
@arrives_in Job arr_seq j ->
forall ρ : work,
is_true (ρ <= @job_cost Job H2 j) ->
is_true (ρ \notin @job_preemptive_points Job H3 j) ->
is_true (first0 (@job_preemptive_points Job H3 j) <= ρ < last0 (@job_preemptive_points Job H3 j))

antidensity_of_preemption_points is not universe polymorphic
Arguments antidensity_of_preemption_points {Job H2 H3} arr_seq H_valid_limited_preemptions_job_model 
  j H_j_arrives ρ _ _
antidensity_of_preemption_points is opaque
Expands to: Constant prosa.analysis.facts.preemption.job.limited.antidensity_of_preemption_points
Declared in library prosa.analysis.facts.preemption.job.limited, line 116, characters 10-42
@antidensity_of_preemption_points
     : forall (Job : JobType) (H2 : JobCost Job) (H3 : JobPreemptionPoints Job)
         (arr_seq : arrival_sequence Job),
       @valid_limited_preemptions_job_model Job H2 H3 arr_seq ->
       forall j : Equality.sort Job,
       @arrives_in Job arr_seq j ->
       forall ρ : work,
       is_true (ρ <= @job_cost Job H2 j) ->
       is_true (ρ \notin @job_preemptive_points Job H3 j) ->
       is_true (first0 (@job_preemptive_points Job H3 j) <= ρ < last0 (@job_preemptive_points Job H3 j))
```

## Lean

```lean
@Prosa.Analysis.Facts.Preemption.Job.Limited.antidensity_of_preemption_points : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobCost Job]
  [inst_2 : Prosa.Model.Preemption.LimitedPreemptive.JobPreemptionPoints Job]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Model.Preemption.LimitedPreemptive.valid_limited_preemptions_job_model arr_seq →
    ∀ (j : Job),
      Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j →
        ∀ ρ ≤ Prosa.Behavior.Job.job_cost j,
          (!decide (ρ ∈ Prosa.Model.Preemption.LimitedPreemptive.job_preemptive_points j)) = true →
            (decide (Prosa.Util.List.first0 (Prosa.Model.Preemption.LimitedPreemptive.job_preemptive_points j) ≤ ρ) &&
                decide (ρ < Prosa.Util.List.last0 (Prosa.Model.Preemption.LimitedPreemptive.job_preemptive_points j))) =
              true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Preemption_Job_Limited_antidensity_of_preemption_points
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
       forall _UU03c1_ : Prosa_Behavior_Job_work,
       LE_le_inst1 Prosa_Behavior_Job_work instLENat _UU03c1_
         (Prosa_Behavior_Job_JobCost_job_cost Job
            inst_3
            inst_6 j) ->
       @eq Bool
         (Bool_not
            (Decidable_decide
               (Membership_mem_inst3 Prosa_Behavior_Job_work (List_inst1 Prosa_Behavior_Job_work)
                  (List_instMembership_inst1 Prosa_Behavior_Job_work)
                  (Prosa_Model_Preemption_LimitedPreemptive_JobPreemptionPoints_job_preemptive_points Job
                     inst_3
                     inst_9 j)
                  _UU03c1_)
               (List_instDecidableMemOfLawfulBEq_inst1 Prosa_Behavior_Job_work
                  (instBEqOfDecidableEq_inst1 Prosa_Behavior_Job_work instDecidableEqNat) Nat_instLawfulBEq
                  _UU03c1_
                  (Prosa_Model_Preemption_LimitedPreemptive_JobPreemptionPoints_job_preemptive_points Job
                     inst_3
                     inst_9 j))))
         Bool_true ->
       @eq Bool
         (Bool_and
            (Decidable_decide
               (LE_le_inst1 Nat instLENat
                  (Prosa_Util_List_first0
                     (Prosa_Model_Preemption_LimitedPreemptive_JobPreemptionPoints_job_preemptive_points Job
                        inst_3
                        inst_9 j))
                  _UU03c1_)
               (Nat_decLe
                  (Prosa_Util_List_first0
                     (Prosa_Model_Preemption_LimitedPreemptive_JobPreemptionPoints_job_preemptive_points Job
                        inst_3
                        inst_9 j))
                  _UU03c1_))
            (Decidable_decide
               (LT_lt_inst1 Prosa_Behavior_Job_work instLTNat _UU03c1_
                  (Prosa_Util_List_last0
                     (Prosa_Model_Preemption_LimitedPreemptive_JobPreemptionPoints_job_preemptive_points Job
                        inst_3
                        inst_9 j)))
               (Nat_decLt _UU03c1_
                  (Prosa_Util_List_last0
                     (Prosa_Model_Preemption_LimitedPreemptive_JobPreemptionPoints_job_preemptive_points Job
                        inst_3
                        inst_9 j)))))
         Bool_true
```
