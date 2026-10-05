# `job_cannot_be_preempted_within_last_segment`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.preemption.rtc_threshold.job_preemptable.job_cannot_be_preempted_within_last_segment`
- Lean: `Prosa.Analysis.Facts.Preemption.RtcThreshold.JobPreemptable.job_cannot_be_preempted_within_last_segment`
- Certificate: `job_cannot_be_preempted_within_last_segment_correspondence`

## Official Rocq

```coq
job_cannot_be_preempted_within_last_segment :
forall {Job : JobType} {H0 : JobCost Job} {H1 : JobPreemptable Job} {PState : ProcessorState Job}
  (arr_seq : arrival_sequence Job) (sched : @schedule Job PState),
@valid_preemption_model Job H0 H1 PState arr_seq sched ->
forall j : Equality.sort Job,
@arrives_in Job arr_seq j ->
forall ρ : duration,
is_true (@job_rtct Job H0 H1 j <= ρ < @job_cost Job H0 j) -> is_true (~~ @job_preemptable Job H1 j ρ)

job_cannot_be_preempted_within_last_segment is not universe polymorphic
Arguments job_cannot_be_preempted_within_last_segment {Job H0 H1 PState} arr_seq 
  sched H_valid_preemption_model j H_j_arrives ρ _
job_cannot_be_preempted_within_last_segment is opaque
Expands to: Constant
            prosa.analysis.facts.preemption.rtc_threshold.job_preemptable.job_cannot_be_preempted_within_last_segment
Declared in library prosa.analysis.facts.preemption.rtc_threshold.job_preemptable, line 210, characters 8-51
@job_cannot_be_preempted_within_last_segment
     : forall (Job : JobType) (H0 : JobCost Job) (H1 : JobPreemptable Job) (PState : ProcessorState Job)
         (arr_seq : arrival_sequence Job) (sched : @schedule Job PState),
       @valid_preemption_model Job H0 H1 PState arr_seq sched ->
       forall j : Equality.sort Job,
       @arrives_in Job arr_seq j ->
       forall ρ : duration,
       is_true (@job_rtct Job H0 H1 j <= ρ < @job_cost Job H0 j) -> is_true (~~ @job_preemptable Job H1 j ρ)
```

## Lean

```lean
@Prosa.Analysis.Facts.Preemption.RtcThreshold.JobPreemptable.job_cannot_be_preempted_within_last_segment : ∀
  {Job : Prosa.Behavior.Job.JobType} [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobCost Job]
  [inst_2 : Prosa.Model.Preemption.Parameter.JobPreemptable Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job}
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job) (sched : Prosa.Behavior.Schedule.schedule PState),
  Prosa.Model.Preemption.Parameter.valid_preemption_model arr_seq sched →
    ∀ (j : Job),
      Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j →
        ∀ (ρ : Prosa.Behavior.Time.duration),
          (decide (Prosa.Model.Preemption.Parameter.job_rtct j ≤ ρ) && decide (ρ < Prosa.Behavior.Job.job_cost j)) =
              true →
            (!Prosa.Model.Preemption.Parameter.job_preemptable j ρ) = true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Preemption_RtcThreshold_JobPreemptable_job_cannot_be_preempted_within_last_segment
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
       forall _UU03c1_ : Prosa_Behavior_Time_duration,
       @eq Bool
         (Bool_and
            (Decidable_decide
               (LE_le_inst1 Nat instLENat
                  (Prosa_Model_Preemption_Parameter_job_rtct Job
                     inst_3
                     inst_6
                     inst_9
                     j)
                  _UU03c1_)
               (Nat_decLe
                  (Prosa_Model_Preemption_Parameter_job_rtct Job
                     inst_3
                     inst_6
                     inst_9
                     j)
                  _UU03c1_))
            (Decidable_decide
               (LT_lt_inst1 Prosa_Behavior_Time_duration instLTNat _UU03c1_
                  (Prosa_Behavior_Job_JobCost_job_cost Job
                     inst_3
                     inst_6
                     j))
               (Nat_decLt _UU03c1_
                  (Prosa_Behavior_Job_JobCost_job_cost Job
                     inst_3
                     inst_6
                     j))))
         Bool_true ->
       @eq Bool
         (Bool_not
            (Prosa_Model_Preemption_Parameter_JobPreemptable_job_preemptable Job
               inst_3
               inst_9
               j _UU03c1_))
         Bool_true
```
