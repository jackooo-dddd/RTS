# `job_last_nonpreemptive_segment_positive`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.preemption.rtc_threshold.job_preemptable.job_last_nonpreemptive_segment_positive`
- Lean: `Prosa.Analysis.Facts.Preemption.RtcThreshold.JobPreemptable.job_last_nonpreemptive_segment_positive`
- Certificate: `job_last_nonpreemptive_segment_positive_correspondence`

## Official Rocq

```coq
job_last_nonpreemptive_segment_positive :
forall {Job : JobType} {H0 : JobCost Job} {H1 : JobPreemptable Job} {PState : ProcessorState Job}
  (arr_seq : arrival_sequence Job) (sched : @schedule Job PState),
@valid_preemption_model Job H0 H1 PState arr_seq sched ->
forall j : Equality.sort Job,
@arrives_in Job arr_seq j ->
is_true (@job_cost_positive Job H0 j) -> is_true (0 < @job_last_nonpreemptive_segment Job H0 H1 j)

job_last_nonpreemptive_segment_positive is not universe polymorphic
Arguments job_last_nonpreemptive_segment_positive {Job H0 H1 PState} arr_seq sched 
  H_valid_preemption_model j H_j_arrives _
job_last_nonpreemptive_segment_positive is opaque
Expands to: Constant
            prosa.analysis.facts.preemption.rtc_threshold.job_preemptable.job_last_nonpreemptive_segment_positive
Declared in library prosa.analysis.facts.preemption.rtc_threshold.job_preemptable, line 119, characters 8-47
@job_last_nonpreemptive_segment_positive
     : forall (Job : JobType) (H0 : JobCost Job) (H1 : JobPreemptable Job) (PState : ProcessorState Job)
         (arr_seq : arrival_sequence Job) (sched : @schedule Job PState),
       @valid_preemption_model Job H0 H1 PState arr_seq sched ->
       forall j : Equality.sort Job,
       @arrives_in Job arr_seq j ->
       is_true (@job_cost_positive Job H0 j) -> is_true (0 < @job_last_nonpreemptive_segment Job H0 H1 j)
```

## Lean

```lean
@Prosa.Analysis.Facts.Preemption.RtcThreshold.JobPreemptable.job_last_nonpreemptive_segment_positive : ∀
  {Job : Prosa.Behavior.Job.JobType} [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobCost Job]
  [inst_2 : Prosa.Model.Preemption.Parameter.JobPreemptable Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job}
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job) (sched : Prosa.Behavior.Schedule.schedule PState),
  Prosa.Model.Preemption.Parameter.valid_preemption_model arr_seq sched →
    ∀ (j : Job),
      Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j →
        Prosa.Model.Job.Properties.job_cost_positive j = true →
          0 < Prosa.Model.Preemption.Parameter.job_last_nonpreemptive_segment j
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Preemption_RtcThreshold_JobPreemptable_job_last_nonpreemptive_segment_positive
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
       @eq Bool
         (Prosa_Model_Job_Properties_job_cost_positive Job
            inst_3
            inst_6 j)
         Bool_true ->
       LT_lt_inst1 Nat instLTNat (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0))
         (Prosa_Model_Preemption_Parameter_job_last_nonpreemptive_segment Job
            inst_3
            inst_6
            inst_9 j)
```
