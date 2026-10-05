# `wc_transform_prefix_inclusion`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.transform.wc_correctness.wc_transform_prefix_inclusion`
- Lean: `Prosa.Analysis.Facts.Transform.WcCorrectness.wc_transform_prefix_inclusion`
- Certificate: `wc_transform_prefix_inclusion_correspondence`

## Official Rocq

```coq
wc_transform_prefix_inclusion :
forall {Job : JobType} {H : JobArrival Job} {H1 : JobDeadline Job} (arr_seq : arrival_sequence Job)
  (sched : @schedule Job (processor_state Job)) (h1 h2 : instant),
is_true (h1 <= h2) ->
forall t : nat,
is_true (t < h1) ->
@wc_transform_prefix Job H H1 arr_seq sched h1 t = @wc_transform_prefix Job H H1 arr_seq sched h2 t

wc_transform_prefix_inclusion is not universe polymorphic
Arguments wc_transform_prefix_inclusion {Job H H1} arr_seq sched h1 h2 H_horizon_order t%nat_scope _
wc_transform_prefix_inclusion is opaque
Expands to: Constant prosa.analysis.facts.transform.wc_correctness.wc_transform_prefix_inclusion
Declared in library prosa.analysis.facts.transform.wc_correctness, line 458, characters 12-41
@wc_transform_prefix_inclusion
     : forall (Job : JobType) (H : JobArrival Job) (H1 : JobDeadline Job) (arr_seq : arrival_sequence Job)
         (sched : @schedule Job (processor_state Job)) (h1 h2 : instant),
       is_true (h1 <= h2) ->
       forall t : nat,
       is_true (t < h1) ->
       @wc_transform_prefix Job H H1 arr_seq sched h1 t = @wc_transform_prefix Job H H1 arr_seq sched h2 t
```

## Lean

```lean
@Prosa.Analysis.Facts.Transform.WcCorrectness.wc_transform_prefix_inclusion : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobArrival Job] [inst_2 : Prosa.Behavior.Job.JobDeadline Job]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job)
  (sched : Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job))
  (h1 h2 : Prosa.Behavior.Time.instant),
  h1 ≤ h2 →
    ∀ t < h1,
      Prosa.Analysis.Transform.WcTrans.wc_transform_prefix arr_seq sched h1 t =
        Prosa.Analysis.Transform.WcTrans.wc_transform_prefix arr_seq sched h2 t
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Transform_WcCorrectness_wc_transform_prefix_inclusion
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : 
          DecidableEq Job)
         (inst_6 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_3)
         (inst_9 : 
          Prosa_Behavior_Job_JobDeadline Job
            inst_3)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_3)
         (sched : Prosa_Behavior_Schedule_schedule_inst4 Job
                    inst_3
                    (Prosa_Model_Processor_Ideal_processor_state Job
                       inst_3))
         (h1 h2 : Prosa_Behavior_Time_instant),
       LE_le_inst1 Prosa_Behavior_Time_instant instLENat h1 h2 ->
       forall t : Nat,
       LT_lt_inst1 Nat instLTNat t h1 ->
       @eq
         (Prosa_Behavior_Schedule_ProcessorState_State_inst2 Job
            inst_3
            (Prosa_Model_Processor_Ideal_processor_state Job
               inst_3))
         (Prosa_Analysis_Transform_WcTrans_wc_transform_prefix Job
            inst_3
            inst_6
            inst_9 arr_seq sched
            h1 t)
         (Prosa_Analysis_Transform_WcTrans_wc_transform_prefix Job
            inst_3
            inst_6
            inst_9 arr_seq sched
            h2 t)
```
