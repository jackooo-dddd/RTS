# `scheduled_jobs_at_uni`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.model.scheduled.scheduled_jobs_at_uni`
- Lean: `Prosa.Analysis.Facts.Model.Scheduled.scheduled_jobs_at_uni`
- Certificate: `scheduled_jobs_at_uni_correspondence`

## Official Rocq

```coq
scheduled_jobs_at_uni :
forall {Job : JobType} {H : JobArrival Job} {PState : ProcessorState Job} (arr_seq : arrival_sequence Job),
@valid_arrival_sequence Job H arr_seq ->
forall sched : @schedule Job PState,
@jobs_come_from_arrival_sequence Job PState sched arr_seq ->
@jobs_must_arrive_to_execute Job H PState sched ->
@uniprocessor_model Job PState ->
forall (j : Equality.sort Job) (t : instant),
(@scheduled_jobs_at Job PState arr_seq sched t == [:: j]) =
(@scheduled_job_at Job PState arr_seq sched t == @Some (Equality.sort Job) j)

scheduled_jobs_at_uni is not universe polymorphic
Arguments scheduled_jobs_at_uni {Job H PState} arr_seq H_valid_arrivals sched
  H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_uni j t
scheduled_jobs_at_uni is opaque
Expands to: Constant prosa.analysis.facts.model.scheduled.scheduled_jobs_at_uni
Declared in library prosa.analysis.facts.model.scheduled, line 136, characters 10-31
@scheduled_jobs_at_uni
     : forall (Job : JobType) (H : JobArrival Job) (PState : ProcessorState Job)
         (arr_seq : arrival_sequence Job),
       @valid_arrival_sequence Job H arr_seq ->
       forall sched : @schedule Job PState,
       @jobs_come_from_arrival_sequence Job PState sched arr_seq ->
       @jobs_must_arrive_to_execute Job H PState sched ->
       @uniprocessor_model Job PState ->
       forall (j : Equality.sort Job) (t : instant),
       (@scheduled_jobs_at Job PState arr_seq sched t == [:: j]) =
       (@scheduled_job_at Job PState arr_seq sched t == @Some (Equality.sort Job) j)
```

## Lean

```lean
@Prosa.Analysis.Facts.Model.Scheduled.scheduled_jobs_at_uni : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobArrival Job]
  {PState : Prosa.Behavior.Schedule.ProcessorState Job}
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
    ∀ (sched : Prosa.Behavior.Schedule.schedule PState),
      Prosa.Behavior.Ready.jobs_come_from_arrival_sequence sched arr_seq →
        Prosa.Behavior.Ready.jobs_must_arrive_to_execute sched →
          Prosa.Model.Processor.PlatformProperties.uniprocessor_model PState →
            ∀ (j : Job) (t : Prosa.Behavior.Time.instant),
              decide (Prosa.Model.Schedule.Scheduled.scheduled_jobs_at arr_seq sched t = [j]) =
                decide (Prosa.Model.Schedule.Scheduled.scheduled_job_at arr_seq sched t = some j)
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_Scheduled_scheduled_jobs_at_uni
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
       forall (j : Job) (t : Prosa_Behavior_Time_instant),
       @eq Bool
         (Decidable_decide
            (@eq (List Job)
               (Prosa_Model_Schedule_Scheduled_scheduled_jobs_at Job
                  inst_3 PState arr_seq
                  sched t)
               (List_cons Job j (List_nil Job)))
            (instDecidableEqList Job
               inst_3
               (Prosa_Model_Schedule_Scheduled_scheduled_jobs_at Job
                  inst_3 PState arr_seq
                  sched t)
               (List_cons Job j (List_nil Job))))
         (Decidable_decide
            (@eq (Option Job)
               (Prosa_Model_Schedule_Scheduled_scheduled_job_at Job
                  inst_3 PState arr_seq
                  sched t)
               (Option_some Job j))
            (Option_instDecidableEq Job
               inst_3
               (Prosa_Model_Schedule_Scheduled_scheduled_job_at Job
                  inst_3 PState arr_seq
                  sched t)
               (Option_some Job j)))
```
