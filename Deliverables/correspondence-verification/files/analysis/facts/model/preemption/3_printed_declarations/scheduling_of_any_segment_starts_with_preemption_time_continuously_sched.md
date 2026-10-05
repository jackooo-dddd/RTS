# `scheduling_of_any_segment_starts_with_preemption_time_continuously_sched`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.model.preemption.scheduling_of_any_segment_starts_with_preemption_time_continuously_sched`
- Lean: `Prosa.Analysis.Facts.Model.Preemption.scheduling_of_any_segment_starts_with_preemption_time_continuously_sched`
- Certificate: `scheduling_of_any_segment_starts_with_preemption_time_continuously_sched_correspondence`

## Official Rocq

```coq
scheduling_of_any_segment_starts_with_preemption_time_continuously_sched :
forall {Job : JobType} {Arrival : JobArrival Job} {Cost : JobCost Job} {PState : ProcessorState Job},
@uniprocessor_model Job PState ->
forall {JobReady0 : @JobReady Job PState Cost Arrival} (arr_seq : arrival_sequence Job),
@valid_arrival_sequence Job Arrival arr_seq ->
forall sched : @schedule Job PState,
@valid_schedule Job Arrival PState sched Cost JobReady0 arr_seq ->
forall {H : JobPreemptable Job},
@valid_preemption_model Job Cost H PState arr_seq sched ->
forall (j : Equality.sort Job) (t1 t2 : nat),
is_true (t1 <= t2) ->
is_true (@preemption_time Job H arr_seq PState sched t1) ->
is_true (@scheduled_at Job PState sched j t2) ->
exists ptst : nat,
  is_true (t1 <= ptst <= t2) /\
  is_true (@preemption_time Job H arr_seq PState sched ptst) /\
  is_true (@scheduled_at Job PState sched j ptst)

scheduling_of_any_segment_starts_with_preemption_time_continuously_sched is not universe polymorphic
Arguments scheduling_of_any_segment_starts_with_preemption_time_continuously_sched 
  {Job Arrival Cost PState} H_uniproc {JobReady0} arr_seq H_valid_arrivals sched 
  H_sched_valid {H} H_valid_preemption_model j (t1 t2)%nat_scope _ _ _
scheduling_of_any_segment_starts_with_preemption_time_continuously_sched is opaque
Expands to: Constant
            prosa.analysis.facts.model.preemption.scheduling_of_any_segment_starts_with_preemption_time_continuously_sched
Declared in library prosa.analysis.facts.model.preemption, line 326, characters 8-80
@scheduling_of_any_segment_starts_with_preemption_time_continuously_sched
     : forall (Job : JobType) (Arrival : JobArrival Job) (Cost : JobCost Job) (PState : ProcessorState Job),
       @uniprocessor_model Job PState ->
       forall (JobReady0 : @JobReady Job PState Cost Arrival) (arr_seq : arrival_sequence Job),
       @valid_arrival_sequence Job Arrival arr_seq ->
       forall sched : @schedule Job PState,
       @valid_schedule Job Arrival PState sched Cost JobReady0 arr_seq ->
       forall H : JobPreemptable Job,
       @valid_preemption_model Job Cost H PState arr_seq sched ->
       forall (j : Equality.sort Job) (t1 t2 : nat),
       is_true (t1 <= t2) ->
       is_true (@preemption_time Job H arr_seq PState sched t1) ->
       is_true (@scheduled_at Job PState sched j t2) ->
       exists ptst : nat,
         is_true (t1 <= ptst <= t2) /\
         is_true (@preemption_time Job H arr_seq PState sched ptst) /\
         is_true (@scheduled_at Job PState sched j ptst)
```

## Lean

```lean
@Prosa.Analysis.Facts.Model.Preemption.scheduling_of_any_segment_starts_with_preemption_time_continuously_sched : ∀
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
                ∀ (j : Job) (t1 t2 : ℕ),
                  t1 ≤ t2 →
                    Prosa.Model.Schedule.PreemptionTime.preemption_time arr_seq sched t1 = true →
                      Prosa.Behavior.Service.scheduled_at sched j t2 = true →
                        ∃ ptst,
                          (decide (t1 ≤ ptst) && decide (ptst ≤ t2)) = true ∧
                            Prosa.Model.Schedule.PreemptionTime.preemption_time arr_seq sched ptst = true ∧
                              Prosa.Behavior.Service.scheduled_at sched j ptst = true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_Preemption_scheduling_of_any_segment_starts_with_preemption_time_continuously_sched
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
       forall (j : Job) (t1 t2 : Nat),
       LE_le_inst1 Nat instLENat t1 t2 ->
       @eq Bool
         (Prosa_Model_Schedule_PreemptionTime_preemption_time Job
            inst_3
            inst_40 arr_seq PState sched
            t1)
         Bool_true ->
       @eq Bool
         (Prosa_Behavior_Service_scheduled_at Job
            inst_3 PState sched j t2)
         Bool_true ->
       Exists Nat
         (fun ptst : Nat =>
          And
            (@eq Bool
               (Bool_and (Decidable_decide (LE_le_inst1 Nat instLENat t1 ptst) (Nat_decLe t1 ptst))
                  (Decidable_decide (LE_le_inst1 Nat instLENat ptst t2) (Nat_decLe ptst t2)))
               Bool_true)
            (And
               (@eq Bool
                  (Prosa_Model_Schedule_PreemptionTime_preemption_time Job
                     inst_3
                     inst_40 arr_seq
                     PState sched ptst)
                  Bool_true)
               (@eq Bool
                  (Prosa_Behavior_Service_scheduled_at Job
                     inst_3 PState sched j
                     ptst)
                  Bool_true)))
```
