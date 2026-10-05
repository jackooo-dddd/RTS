# `neq_scheduled_at_pt`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.model.preemption.neq_scheduled_at_pt`
- Lean: `Prosa.Analysis.Facts.Model.Preemption.neq_scheduled_at_pt`
- Certificate: `neq_scheduled_at_pt_correspondence`

## Official Rocq

```coq
neq_scheduled_at_pt :
forall {Job : JobType} {H : JobArrival Job} {H0 : JobCost Job} {H1 : JobPreemptable Job}
  (arr_seq : arrival_sequence Job),
@valid_arrival_sequence Job H arr_seq ->
forall {PState : ProcessorState Job},
@uniprocessor_model Job PState ->
forall sched : @schedule Job PState,
@jobs_come_from_arrival_sequence Job PState sched arr_seq ->
@jobs_must_arrive_to_execute Job H PState sched ->
@valid_preemption_model Job H0 H1 PState arr_seq sched ->
forall (j : Equality.sort Job) (t : instant),
is_true (@scheduled_at Job PState sched j t) ->
forall (j' : Equality.sort Job) (t' : instant),
is_true (@scheduled_at Job PState sched j' t') ->
is_true (j != j') ->
is_true (t <= t') ->
exists2 pt : instant, is_true (@preemption_time Job H1 arr_seq PState sched pt) & is_true (t < pt <= t')

neq_scheduled_at_pt is not universe polymorphic
Arguments neq_scheduled_at_pt {Job H H0 H1} arr_seq H_valid_arrivals {PState} H_uniproc 
  sched H_jobs_come_from_arrival_sequence H_must_arrive H_valid_preemption_model 
  j t _ j' t' _ _ _
neq_scheduled_at_pt is opaque
Expands to: Constant prosa.analysis.facts.model.preemption.neq_scheduled_at_pt
Declared in library prosa.analysis.facts.model.preemption, line 182, characters 8-27
@neq_scheduled_at_pt
     : forall (Job : JobType) (H : JobArrival Job) (H0 : JobCost Job) (H1 : JobPreemptable Job)
         (arr_seq : arrival_sequence Job),
       @valid_arrival_sequence Job H arr_seq ->
       forall PState : ProcessorState Job,
       @uniprocessor_model Job PState ->
       forall sched : @schedule Job PState,
       @jobs_come_from_arrival_sequence Job PState sched arr_seq ->
       @jobs_must_arrive_to_execute Job H PState sched ->
       @valid_preemption_model Job H0 H1 PState arr_seq sched ->
       forall (j : Equality.sort Job) (t : instant),
       is_true (@scheduled_at Job PState sched j t) ->
       forall (j' : Equality.sort Job) (t' : instant),
       is_true (@scheduled_at Job PState sched j' t') ->
       is_true (j != j') ->
       is_true (t <= t') ->
       exists2 pt : instant,
         is_true (@preemption_time Job H1 arr_seq PState sched pt) & is_true (t < pt <= t')
```

## Lean

```lean
@Prosa.Analysis.Facts.Model.Preemption.neq_scheduled_at_pt : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobArrival Job] [inst_2 : Prosa.Behavior.Job.JobCost Job]
  [inst_3 : Prosa.Model.Preemption.Parameter.JobPreemptable Job]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
    ∀ (PState : Prosa.Behavior.Schedule.ProcessorState Job),
      Prosa.Model.Processor.PlatformProperties.uniprocessor_model PState →
        ∀ (sched : Prosa.Behavior.Schedule.schedule PState),
          Prosa.Behavior.Ready.jobs_come_from_arrival_sequence sched arr_seq →
            Prosa.Behavior.Ready.jobs_must_arrive_to_execute sched →
              Prosa.Model.Preemption.Parameter.valid_preemption_model arr_seq sched →
                ∀ (j : Job) (t : Prosa.Behavior.Time.instant),
                  Prosa.Behavior.Service.scheduled_at sched j t = true →
                    ∀ (j' : Job) (t' : Prosa.Behavior.Time.instant),
                      Prosa.Behavior.Service.scheduled_at sched j' t' = true →
                        decide (j ≠ j') = true →
                          t ≤ t' →
                            ∃ pt,
                              Prosa.Model.Schedule.PreemptionTime.preemption_time arr_seq sched pt = true ∧
                                (decide (t < pt) && decide (pt ≤ t')) = true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_Preemption_neq_scheduled_at_pt
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (inst_6 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_3)
         (inst_9 : 
          Prosa_Behavior_Job_JobCost Job
            inst_3)
         (inst_12 : 
          Prosa_Model_Preemption_Parameter_JobPreemptable Job
            inst_3)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_3),
       Prosa_Behavior_Arrival_sequence_valid_arrival_sequence Job
         inst_3
         inst_6 arr_seq ->
       forall
         PState : Prosa_Behavior_Schedule_ProcessorState Job
                    inst_3,
       Prosa_Model_Processor_PlatformProperties_uniprocessor_model Job
         inst_3 PState ->
       forall
         sched : Prosa_Behavior_Schedule_schedule Job
                   inst_3 PState,
       Prosa_Behavior_Ready_jobs_come_from_arrival_sequence Job
         inst_3 PState sched arr_seq ->
       Prosa_Behavior_Ready_jobs_must_arrive_to_execute Job
         inst_3
         inst_6 PState sched ->
       Prosa_Model_Preemption_Parameter_valid_preemption_model Job
         inst_3
         inst_9
         inst_12 PState arr_seq sched ->
       forall (j : Job) (t : Prosa_Behavior_Time_instant),
       @eq Bool
         (Prosa_Behavior_Service_scheduled_at Job
            inst_3 PState sched j t)
         Bool_true ->
       forall (j' : Job) (t' : Prosa_Behavior_Time_instant),
       @eq Bool
         (Prosa_Behavior_Service_scheduled_at Job
            inst_3 PState sched j' t')
         Bool_true ->
       @eq Bool
         (Decidable_decide (Ne Job j j')
            (instDecidableNot (@eq Job j j')
               (inst_3 j j')))
         Bool_true ->
       LE_le_inst1 Prosa_Behavior_Time_instant instLENat t t' ->
       Exists Prosa_Behavior_Time_instant
         (fun pt : Prosa_Behavior_Time_instant =>
          And
            (@eq Bool
               (Prosa_Model_Schedule_PreemptionTime_preemption_time Job
                  inst_3
                  inst_12 arr_seq PState
                  sched pt)
               Bool_true)
            (@eq Bool
               (Bool_and
                  (Decidable_decide (LT_lt_inst1 Prosa_Behavior_Time_instant instLTNat t pt) (Nat_decLt t pt))
                  (Decidable_decide (LE_le_inst1 Prosa_Behavior_Time_instant instLENat pt t')
                     (Nat_decLe pt t')))
               Bool_true))
```
