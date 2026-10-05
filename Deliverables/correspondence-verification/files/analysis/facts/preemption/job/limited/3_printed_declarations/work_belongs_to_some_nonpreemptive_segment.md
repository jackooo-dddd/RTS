# `work_belongs_to_some_nonpreemptive_segment`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.preemption.job.limited.work_belongs_to_some_nonpreemptive_segment`
- Lean: `Prosa.Analysis.Facts.Preemption.Job.Limited.work_belongs_to_some_nonpreemptive_segment`
- Certificate: `work_belongs_to_some_nonpreemptive_segment_correspondence`

## Official Rocq

```coq
work_belongs_to_some_nonpreemptive_segment :
forall {Job : JobType} {H2 : JobCost Job} {H3 : JobPreemptionPoints Job} (arr_seq : arrival_sequence Job),
@valid_limited_preemptions_job_model Job H2 H3 arr_seq ->
forall j : Equality.sort Job,
@arrives_in Job arr_seq j ->
forall ρ : work,
is_true (ρ <= @job_cost Job H2 j) ->
is_true (ρ \notin @job_preemptive_points Job H3 j) ->
exists n : nat,
  is_true (n.+1 < @size work (@job_preemptive_points Job H3 j)) /\
  is_true
    (@nth nat 0 (@job_preemptive_points Job H3 j) n < ρ < @nth nat 0 (@job_preemptive_points Job H3 j) n.+1)

work_belongs_to_some_nonpreemptive_segment is not universe polymorphic
Arguments work_belongs_to_some_nonpreemptive_segment {Job H2 H3} arr_seq
  H_valid_limited_preemptions_job_model j H_j_arrives ρ _ _
work_belongs_to_some_nonpreemptive_segment is opaque
Expands to: Constant prosa.analysis.facts.preemption.job.limited.work_belongs_to_some_nonpreemptive_segment
Declared in library prosa.analysis.facts.preemption.job.limited, line 137, characters 10-52
@work_belongs_to_some_nonpreemptive_segment
     : forall (Job : JobType) (H2 : JobCost Job) (H3 : JobPreemptionPoints Job)
         (arr_seq : arrival_sequence Job),
       @valid_limited_preemptions_job_model Job H2 H3 arr_seq ->
       forall j : Equality.sort Job,
       @arrives_in Job arr_seq j ->
       forall ρ : work,
       is_true (ρ <= @job_cost Job H2 j) ->
       is_true (ρ \notin @job_preemptive_points Job H3 j) ->
       exists n : nat,
         is_true (n.+1 < @size work (@job_preemptive_points Job H3 j)) /\
         is_true
           (@nth nat 0 (@job_preemptive_points Job H3 j) n < ρ <
            @nth nat 0 (@job_preemptive_points Job H3 j) n.+1)
```

## Lean

```lean
@Prosa.Analysis.Facts.Preemption.Job.Limited.work_belongs_to_some_nonpreemptive_segment : ∀
  {Job : Prosa.Behavior.Job.JobType} [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobCost Job]
  [inst_2 : Prosa.Model.Preemption.LimitedPreemptive.JobPreemptionPoints Job]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Model.Preemption.LimitedPreemptive.valid_limited_preemptions_job_model arr_seq →
    ∀ (j : Job),
      Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j →
        ∀ ρ ≤ Prosa.Behavior.Job.job_cost j,
          (!decide (ρ ∈ Prosa.Model.Preemption.LimitedPreemptive.job_preemptive_points j)) = true →
            ∃ n,
              n + 1 < (Prosa.Model.Preemption.LimitedPreemptive.job_preemptive_points j).length ∧
                (decide ((Prosa.Model.Preemption.LimitedPreemptive.job_preemptive_points j).getD n 0 < ρ) &&
                    decide (ρ < (Prosa.Model.Preemption.LimitedPreemptive.job_preemptive_points j).getD (n + 1) 0)) =
                  true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Preemption_Job_Limited_work_belongs_to_some_nonpreemptive_segment
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
       Exists Nat
         (fun n : Nat =>
          And
            (LT_lt_inst1 Nat instLTNat
               (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat) n
                  (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1)))
               (List_length_inst1 Prosa_Behavior_Job_work
                  (Prosa_Model_Preemption_LimitedPreemptive_JobPreemptionPoints_job_preemptive_points Job
                     inst_3
                     inst_9 j)))
            (@eq Bool
               (Bool_and
                  (Decidable_decide
                     (LT_lt_inst1 Prosa_Behavior_Job_work instLTNat
                        (List_getD_inst1 Prosa_Behavior_Job_work
                           (Prosa_Model_Preemption_LimitedPreemptive_JobPreemptionPoints_job_preemptive_points
                              Job
                              inst_3
                              inst_9
                              j)
                           n (OfNat_ofNat_inst1 Prosa_Behavior_Job_work 0 (instOfNatNat 0)))
                        _UU03c1_)
                     (Nat_decLt
                        (List_getD_inst1 Prosa_Behavior_Job_work
                           (Prosa_Model_Preemption_LimitedPreemptive_JobPreemptionPoints_job_preemptive_points
                              Job
                              inst_3
                              inst_9
                              j)
                           n (OfNat_ofNat_inst1 Prosa_Behavior_Job_work 0 (instOfNatNat 0)))
                        _UU03c1_))
                  (Decidable_decide
                     (LT_lt_inst1 Prosa_Behavior_Job_work instLTNat _UU03c1_
                        (List_getD_inst1 Prosa_Behavior_Job_work
                           (Prosa_Model_Preemption_LimitedPreemptive_JobPreemptionPoints_job_preemptive_points
                              Job
                              inst_3
                              inst_9
                              j)
                           (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat) n
                              (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1)))
                           (OfNat_ofNat_inst1 Prosa_Behavior_Job_work 0 (instOfNatNat 0))))
                     (Nat_decLt _UU03c1_
                        (List_getD_inst1 Prosa_Behavior_Job_work
                           (Prosa_Model_Preemption_LimitedPreemptive_JobPreemptionPoints_job_preemptive_points
                              Job
                              inst_3
                              inst_9
                              j)
                           (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat) n
                              (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1)))
                           (OfNat_ofNat_inst1 Prosa_Behavior_Job_work 0 (instOfNatNat 0))))))
               Bool_true))
```
