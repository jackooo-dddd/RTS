# `scheduled_jobs_at_seq1`

- Kind (Rocq): Corollary
- Rocq: `prosa.analysis.facts.model.scheduled.scheduled_jobs_at_seq1`
- Lean: `Prosa.Analysis.Facts.Model.Scheduled.scheduled_jobs_at_seq1`
- Certificate: `scheduled_jobs_at_seq1_correspondence`

## Official Rocq

```coq
scheduled_jobs_at_seq1 :
forall {Job : JobType} {H : JobArrival Job} {PState : ProcessorState Job} (arr_seq : arrival_sequence Job),
@valid_arrival_sequence Job H arr_seq ->
forall sched : @schedule Job PState,
@jobs_come_from_arrival_sequence Job PState sched arr_seq ->
@jobs_must_arrive_to_execute Job H PState sched ->
@uniprocessor_model Job PState ->
forall t : instant, is_true (@size (Equality.sort Job) (@scheduled_jobs_at Job PState arr_seq sched t) <= 1)

scheduled_jobs_at_seq1 is not universe polymorphic
Arguments scheduled_jobs_at_seq1 {Job H PState} arr_seq H_valid_arrivals sched
  H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_uni t
scheduled_jobs_at_seq1 is opaque
Expands to: Constant prosa.analysis.facts.model.scheduled.scheduled_jobs_at_seq1
Declared in library prosa.analysis.facts.model.scheduled, line 111, characters 14-36
@scheduled_jobs_at_seq1
     : forall (Job : JobType) (H : JobArrival Job) (PState : ProcessorState Job)
         (arr_seq : arrival_sequence Job),
       @valid_arrival_sequence Job H arr_seq ->
       forall sched : @schedule Job PState,
       @jobs_come_from_arrival_sequence Job PState sched arr_seq ->
       @jobs_must_arrive_to_execute Job H PState sched ->
       @uniprocessor_model Job PState ->
       forall t : instant,
       is_true (@size (Equality.sort Job) (@scheduled_jobs_at Job PState arr_seq sched t) <= 1)
```

## Lean

```lean
@Prosa.Analysis.Facts.Model.Scheduled.scheduled_jobs_at_seq1 : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobArrival Job]
  {PState : Prosa.Behavior.Schedule.ProcessorState Job}
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
    ∀ (sched : Prosa.Behavior.Schedule.schedule PState),
      Prosa.Behavior.Ready.jobs_come_from_arrival_sequence sched arr_seq →
        Prosa.Behavior.Ready.jobs_must_arrive_to_execute sched →
          Prosa.Model.Processor.PlatformProperties.uniprocessor_model PState →
            ∀ (t : Prosa.Behavior.Time.instant),
              (Prosa.Model.Schedule.Scheduled.scheduled_jobs_at arr_seq sched t).length ≤ 1
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_Scheduled_scheduled_jobs_at_seq1
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (inst_6 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_3)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_3),
       Prosa_Behavior_Arrival_sequence_valid_arrival_sequence Job
         inst_3
         inst_6 arr_seq ->
       forall
         sched : Prosa_Behavior_Schedule_schedule Job
                   inst_3 PState,
       Prosa_Behavior_Ready_jobs_come_from_arrival_sequence Job
         inst_3 PState sched arr_seq ->
       Prosa_Behavior_Ready_jobs_must_arrive_to_execute Job
         inst_3
         inst_6 PState sched ->
       Prosa_Model_Processor_PlatformProperties_uniprocessor_model Job
         inst_3 PState ->
       forall t : Prosa_Behavior_Time_instant,
       LE_le_inst1 Nat instLENat
         (List_length Job
            (Prosa_Model_Schedule_Scheduled_scheduled_jobs_at Job
               inst_3 PState arr_seq sched
               t))
         (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1))
```
