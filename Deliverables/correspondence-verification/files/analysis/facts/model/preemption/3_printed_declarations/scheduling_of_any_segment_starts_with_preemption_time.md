# `scheduling_of_any_segment_starts_with_preemption_time`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.model.preemption.scheduling_of_any_segment_starts_with_preemption_time`
- Lean: `Prosa.Analysis.Facts.Model.Preemption.scheduling_of_any_segment_starts_with_preemption_time`
- Certificate: `scheduling_of_any_segment_starts_with_preemption_time_correspondence`

## Official Rocq

```coq
scheduling_of_any_segment_starts_with_preemption_time :
forall {Job : JobType} {Arrival : JobArrival Job} {Cost : JobCost Job} {PState : ProcessorState Job},
@uniprocessor_model Job PState ->
forall {JobReady0 : @JobReady Job PState Cost Arrival} (arr_seq : arrival_sequence Job),
@valid_arrival_sequence Job Arrival arr_seq ->
forall sched : @schedule Job PState,
@valid_schedule Job Arrival PState sched Cost JobReady0 arr_seq ->
forall {H : JobPreemptable Job},
@valid_preemption_model Job Cost H PState arr_seq sched ->
forall (j : Equality.sort Job) (t : instant),
is_true (@scheduled_at Job PState sched j t) ->
exists pt : nat,
  is_true (@job_arrival Job Arrival j <= pt <= t) /\
  is_true (@preemption_time Job H arr_seq PState sched pt) /\
  (forall t' : nat, is_true (pt <= t' <= t) -> is_true (@scheduled_at Job PState sched j t'))

scheduling_of_any_segment_starts_with_preemption_time is not universe polymorphic
Arguments scheduling_of_any_segment_starts_with_preemption_time {Job Arrival Cost PState} 
  H_uniproc {JobReady0} arr_seq H_valid_arrivals sched H_sched_valid {H} H_valid_preemption_model 
  j t _
scheduling_of_any_segment_starts_with_preemption_time is opaque
Expands to: Constant
            prosa.analysis.facts.model.preemption.scheduling_of_any_segment_starts_with_preemption_time
Declared in library prosa.analysis.facts.model.preemption, line 280, characters 8-61
@scheduling_of_any_segment_starts_with_preemption_time
     : forall (Job : JobType) (Arrival : JobArrival Job) (Cost : JobCost Job) (PState : ProcessorState Job),
       @uniprocessor_model Job PState ->
       forall (JobReady0 : @JobReady Job PState Cost Arrival) (arr_seq : arrival_sequence Job),
       @valid_arrival_sequence Job Arrival arr_seq ->
       forall sched : @schedule Job PState,
       @valid_schedule Job Arrival PState sched Cost JobReady0 arr_seq ->
       forall H : JobPreemptable Job,
       @valid_preemption_model Job Cost H PState arr_seq sched ->
       forall (j : Equality.sort Job) (t : instant),
       is_true (@scheduled_at Job PState sched j t) ->
       exists pt : nat,
         is_true (@job_arrival Job Arrival j <= pt <= t) /\
         is_true (@preemption_time Job H arr_seq PState sched pt) /\
         (forall t' : nat, is_true (pt <= t' <= t) -> is_true (@scheduled_at Job PState sched j t'))
```

## Lean

```lean
@Prosa.Analysis.Facts.Model.Preemption.scheduling_of_any_segment_starts_with_preemption_time : ∀
  {Job : Prosa.Behavior.Job.JobType} [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobArrival Job]
  [inst_2 : Prosa.Behavior.Job.JobCost Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job},
  Prosa.Model.Processor.PlatformProperties.uniprocessor_model PState →
    ∀ [inst_3 : Prosa.Behavior.Ready.JobReady Job PState]
      (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
      Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
        ∀ (sched : Prosa.Behavior.Schedule.schedule PState),
          Prosa.Behavior.Ready.valid_schedule sched arr_seq →
            ∀ [inst_4 : Prosa.Model.Preemption.Parameter.JobPreemptable Job],
              Prosa.Model.Preemption.Parameter.valid_preemption_model arr_seq sched →
                ∀ (j : Job) (t : Prosa.Behavior.Time.instant),
                  Prosa.Behavior.Service.scheduled_at sched j t = true →
                    ∃ pt,
                      (decide (Prosa.Behavior.Job.job_arrival j ≤ pt) && decide (pt ≤ t)) = true ∧
                        Prosa.Model.Schedule.PreemptionTime.preemption_time arr_seq sched pt = true ∧
                          ∀ (t' : ℕ),
                            (decide (pt ≤ t') && decide (t' ≤ t)) = true →
                              Prosa.Behavior.Service.scheduled_at sched j t' = true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_Preemption_scheduling_of_any_segment_starts_with_preemption_time
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (inst_6 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_3)
         (inst_9 : 
          Prosa_Behavior_Job_JobCost Job
            inst_3)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3),
       Prosa_Model_Processor_PlatformProperties_uniprocessor_model Job
         inst_3 PState ->
       forall
         (inst_19 : 
          Prosa_Behavior_Ready_JobReady Job
            inst_3 PState
            inst_9
            inst_6)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_3),
       Prosa_Behavior_Arrival_sequence_valid_arrival_sequence Job
         inst_3
         inst_6 arr_seq ->
       forall
         sched : Prosa_Behavior_Schedule_schedule Job
                   inst_3 PState,
       Prosa_Behavior_Ready_valid_schedule Job
         inst_3
         inst_6 PState sched
         inst_9
         inst_19 arr_seq ->
       forall
         inst_40 : 
          Prosa_Model_Preemption_Parameter_JobPreemptable Job
            inst_3,
       Prosa_Model_Preemption_Parameter_valid_preemption_model Job
         inst_3
         inst_9
         inst_40 PState arr_seq sched ->
       forall (j : Job) (t : Prosa_Behavior_Time_instant),
       @eq Bool
         (Prosa_Behavior_Service_scheduled_at Job
            inst_3 PState sched j t)
         Bool_true ->
       Exists Nat
         (fun pt : Nat =>
          And
            (@eq Bool
               (Bool_and
                  (Decidable_decide
                     (LE_le_inst1 Prosa_Behavior_Time_instant instLENat
                        (Prosa_Behavior_Job_JobArrival_job_arrival Job
                           inst_3
                           inst_6 j)
                        pt)
                     (Nat_decLe
                        (Prosa_Behavior_Job_JobArrival_job_arrival Job
                           inst_3
                           inst_6 j)
                        pt))
                  (Decidable_decide (LE_le_inst1 Nat instLENat pt t) (Nat_decLe pt t)))
               Bool_true)
            (And
               (@eq Bool
                  (Prosa_Model_Schedule_PreemptionTime_preemption_time Job
                     inst_3
                     inst_40 arr_seq
                     PState sched pt)
                  Bool_true)
               (forall t' : Nat,
                @eq Bool
                  (Bool_and (Decidable_decide (LE_le_inst1 Nat instLENat pt t') (Nat_decLe pt t'))
                     (Decidable_decide (LE_le_inst1 Nat instLENat t' t) (Nat_decLe t' t)))
                  Bool_true ->
                @eq Bool
                  (Prosa_Behavior_Service_scheduled_at Job
                     inst_3 PState sched
                     j t')
                  Bool_true)))
```
