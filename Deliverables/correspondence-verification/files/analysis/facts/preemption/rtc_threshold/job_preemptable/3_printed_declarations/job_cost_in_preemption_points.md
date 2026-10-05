# `job_cost_in_preemption_points`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.preemption.rtc_threshold.job_preemptable.job_cost_in_preemption_points`
- Lean: `Prosa.Analysis.Facts.Preemption.RtcThreshold.JobPreemptable.job_cost_in_preemption_points`
- Certificate: `job_cost_in_preemption_points_correspondence`

## Official Rocq

```coq
job_cost_in_preemption_points :
forall {Job : JobType} {H0 : JobCost Job} {H1 : JobPreemptable Job} {PState : ProcessorState Job}
  (arr_seq : arrival_sequence Job) (sched : @schedule Job PState),
@valid_preemption_model Job H0 H1 PState arr_seq sched ->
forall j : Equality.sort Job,
@arrives_in Job arr_seq j ->
is_true (0 < @job_cost Job H0 j) -> is_true (@job_cost Job H0 j \in @job_preemption_points Job H0 H1 j)

job_cost_in_preemption_points is not universe polymorphic
Arguments job_cost_in_preemption_points {Job H0 H1 PState} arr_seq sched H_valid_preemption_model 
  j H_j_arrives _
job_cost_in_preemption_points is opaque
Expands to: Constant
            prosa.analysis.facts.preemption.rtc_threshold.job_preemptable.job_cost_in_preemption_points
Declared in library prosa.analysis.facts.preemption.rtc_threshold.job_preemptable, line 65, characters 8-37
@job_cost_in_preemption_points
     : forall (Job : JobType) (H0 : JobCost Job) (H1 : JobPreemptable Job) (PState : ProcessorState Job)
         (arr_seq : arrival_sequence Job) (sched : @schedule Job PState),
       @valid_preemption_model Job H0 H1 PState arr_seq sched ->
       forall j : Equality.sort Job,
       @arrives_in Job arr_seq j ->
       is_true (0 < @job_cost Job H0 j) ->
       is_true (@job_cost Job H0 j \in @job_preemption_points Job H0 H1 j)
```

## Lean

```lean
@Prosa.Analysis.Facts.Preemption.RtcThreshold.JobPreemptable.job_cost_in_preemption_points : ∀
  {Job : Prosa.Behavior.Job.JobType} [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobCost Job]
  [inst_2 : Prosa.Model.Preemption.Parameter.JobPreemptable Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job}
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job) (sched : Prosa.Behavior.Schedule.schedule PState),
  Prosa.Model.Preemption.Parameter.valid_preemption_model arr_seq sched →
    ∀ (j : Job),
      Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j →
        0 < Prosa.Behavior.Job.job_cost j →
          decide (Prosa.Behavior.Job.job_cost j ∈ Prosa.Model.Preemption.Parameter.job_preemption_points j) = true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Preemption_RtcThreshold_JobPreemptable_job_cost_in_preemption_points
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : 
          DecidableEq Job)
         (inst_6 : 
          Prosa_Behavior_Job_JobCost Job
            inst_3)
         (inst_9 : 
          Prosa_Model_Preemption_Parameter_JobPreemptable Job
            inst_3)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_3)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3
                    PState),
       Prosa_Model_Preemption_Parameter_valid_preemption_model Job
         inst_3
         inst_6
         inst_9
         PState arr_seq sched ->
       forall j : Job,
       Prosa_Behavior_Arrival_sequence_arrives_in Job
         inst_3
         arr_seq j ->
       LT_lt_inst1 Prosa_Behavior_Job_work instLTNat
         (OfNat_ofNat_inst1 Prosa_Behavior_Job_work 0 (instOfNatNat 0))
         (Prosa_Behavior_Job_JobCost_job_cost Job
            inst_3
            inst_6
            j) ->
       @eq Bool
         (Decidable_decide
            (Membership_mem_inst3 Prosa_Behavior_Job_work (List_inst1 Prosa_Behavior_Job_work)
               (List_instMembership_inst1 Prosa_Behavior_Job_work)
               (Prosa_Model_Preemption_Parameter_job_preemption_points Job
                  inst_3
                  inst_6
                  inst_9
                  j)
               (Prosa_Behavior_Job_JobCost_job_cost Job
                  inst_3
                  inst_6
                  j))
            (List_instDecidableMemOfLawfulBEq_inst1 Prosa_Behavior_Job_work
               (instBEqOfDecidableEq_inst1 Prosa_Behavior_Job_work instDecidableEqNat) Nat_instLawfulBEq
               (Prosa_Behavior_Job_JobCost_job_cost Job
                  inst_3
                  inst_6
                  j)
               (Prosa_Model_Preemption_Parameter_job_preemption_points Job
                  inst_3
                  inst_6
                  inst_9
                  j)))
         Bool_true
```
