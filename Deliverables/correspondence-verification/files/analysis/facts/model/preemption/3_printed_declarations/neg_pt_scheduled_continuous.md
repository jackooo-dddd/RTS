# `neg_pt_scheduled_continuous`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.model.preemption.neg_pt_scheduled_continuous`
- Lean: `Prosa.Analysis.Facts.Model.Preemption.neg_pt_scheduled_continuous`
- Certificate: `neg_pt_scheduled_continuous_correspondence`

## Official Rocq

```coq
neg_pt_scheduled_continuous :
forall {Job : JobType} {H : JobArrival Job} {H0 : JobCost Job} {H1 : JobPreemptable Job}
  (arr_seq : arrival_sequence Job),
@valid_arrival_sequence Job H arr_seq ->
forall {PState : ProcessorState Job},
@uniprocessor_model Job PState ->
forall sched : @schedule Job PState,
@jobs_come_from_arrival_sequence Job PState sched arr_seq ->
@jobs_must_arrive_to_execute Job H PState sched ->
@valid_preemption_model Job H0 H1 PState arr_seq sched ->
forall (j : Equality.sort Job) (t1 t2 t t' : nat),
is_true (t1 <= t < t2) ->
is_true (t1 <= t' < t2) ->
(forall t0 : nat, is_true (t1 <= t0 < t2) -> is_true (~~ @preemption_time Job H1 arr_seq PState sched t0)) ->
is_true (@scheduled_at Job PState sched j t) -> is_true (@scheduled_at Job PState sched j t')

neg_pt_scheduled_continuous is not universe polymorphic
Arguments neg_pt_scheduled_continuous {Job H H0 H1} arr_seq H_valid_arrivals {PState} 
  H_uniproc sched H_jobs_come_from_arrival_sequence H_must_arrive H_valid_preemption_model 
  j (t1 t2 t t')%nat_scope _ _ _%function_scope _
neg_pt_scheduled_continuous is opaque
Expands to: Constant prosa.analysis.facts.model.preemption.neg_pt_scheduled_continuous
Declared in library prosa.analysis.facts.model.preemption, line 160, characters 8-35
@neg_pt_scheduled_continuous
     : forall (Job : JobType) (H : JobArrival Job) (H0 : JobCost Job) (H1 : JobPreemptable Job)
         (arr_seq : arrival_sequence Job),
       @valid_arrival_sequence Job H arr_seq ->
       forall PState : ProcessorState Job,
       @uniprocessor_model Job PState ->
       forall sched : @schedule Job PState,
       @jobs_come_from_arrival_sequence Job PState sched arr_seq ->
       @jobs_must_arrive_to_execute Job H PState sched ->
       @valid_preemption_model Job H0 H1 PState arr_seq sched ->
       forall (j : Equality.sort Job) (t1 t2 t t' : nat),
       is_true (t1 <= t < t2) ->
       is_true (t1 <= t' < t2) ->
       (forall t0 : nat,
        is_true (t1 <= t0 < t2) -> is_true (~~ @preemption_time Job H1 arr_seq PState sched t0)) ->
       is_true (@scheduled_at Job PState sched j t) -> is_true (@scheduled_at Job PState sched j t')
```

## Lean

```lean
@Prosa.Analysis.Facts.Model.Preemption.neg_pt_scheduled_continuous : ∀ {Job : Prosa.Behavior.Job.JobType}
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
                ∀ (j : Job) (t1 t2 t t' : ℕ),
                  (decide (t1 ≤ t) && decide (t < t2)) = true →
                    (decide (t1 ≤ t') && decide (t' < t2)) = true →
                      (∀ (t0 : ℕ),
                          (decide (t1 ≤ t0) && decide (t0 < t2)) = true →
                            (!Prosa.Model.Schedule.PreemptionTime.preemption_time arr_seq sched t0) = true) →
                        Prosa.Behavior.Service.scheduled_at sched j t = true →
                          Prosa.Behavior.Service.scheduled_at sched j t' = true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_Preemption_neg_pt_scheduled_continuous
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
       forall (j : Job) (t1 t2 t t' : Nat),
       @eq Bool
         (Bool_and (Decidable_decide (LE_le_inst1 Nat instLENat t1 t) (Nat_decLe t1 t))
            (Decidable_decide (LT_lt_inst1 Nat instLTNat t t2) (Nat_decLt t t2)))
         Bool_true ->
       @eq Bool
         (Bool_and (Decidable_decide (LE_le_inst1 Nat instLENat t1 t') (Nat_decLe t1 t'))
            (Decidable_decide (LT_lt_inst1 Nat instLTNat t' t2) (Nat_decLt t' t2)))
         Bool_true ->
       (forall t0 : Nat,
        @eq Bool
          (Bool_and (Decidable_decide (LE_le_inst1 Nat instLENat t1 t0) (Nat_decLe t1 t0))
             (Decidable_decide (LT_lt_inst1 Nat instLTNat t0 t2) (Nat_decLt t0 t2)))
          Bool_true ->
        @eq Bool
          (Bool_not
             (Prosa_Model_Schedule_PreemptionTime_preemption_time Job
                inst_3
                inst_12 arr_seq PState
                sched t0))
          Bool_true) ->
       @eq Bool
         (Prosa_Behavior_Service_scheduled_at Job
            inst_3 PState sched j t)
         Bool_true ->
       @eq Bool
         (Prosa_Behavior_Service_scheduled_at Job
            inst_3 PState sched j t')
         Bool_true
```
