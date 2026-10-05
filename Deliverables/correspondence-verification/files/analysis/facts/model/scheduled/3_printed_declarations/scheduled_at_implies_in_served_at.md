# `scheduled_at_implies_in_served_at`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.model.scheduled.scheduled_at_implies_in_served_at`
- Lean: `Prosa.Analysis.Facts.Model.Scheduled.scheduled_at_implies_in_served_at`
- Certificate: `scheduled_at_implies_in_served_at_correspondence`

## Official Rocq

```coq
scheduled_at_implies_in_served_at :
forall {Job : JobType} {H : JobArrival Job} {PState : ProcessorState Job} (arr_seq : arrival_sequence Job),
@valid_arrival_sequence Job H arr_seq ->
forall sched : @schedule Job PState,
@jobs_come_from_arrival_sequence Job PState sched arr_seq ->
@jobs_must_arrive_to_execute Job H PState sched ->
@ideal_progress_proc_model Job PState ->
forall (j : Equality.sort Job) (t : instant),
is_true (@scheduled_at Job PState sched j t) -> is_true (j \in @served_jobs_at Job PState arr_seq sched t)

scheduled_at_implies_in_served_at is not universe polymorphic
Arguments scheduled_at_implies_in_served_at {Job H PState} arr_seq H_valid_arrivals 
  sched H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_ideal_progress_model 
  j t _
scheduled_at_implies_in_served_at is opaque
Expands to: Constant prosa.analysis.facts.model.scheduled.scheduled_at_implies_in_served_at
Declared in library prosa.analysis.facts.model.scheduled, line 88, characters 10-43
@scheduled_at_implies_in_served_at
     : forall (Job : JobType) (H : JobArrival Job) (PState : ProcessorState Job)
         (arr_seq : arrival_sequence Job),
       @valid_arrival_sequence Job H arr_seq ->
       forall sched : @schedule Job PState,
       @jobs_come_from_arrival_sequence Job PState sched arr_seq ->
       @jobs_must_arrive_to_execute Job H PState sched ->
       @ideal_progress_proc_model Job PState ->
       forall (j : Equality.sort Job) (t : instant),
       is_true (@scheduled_at Job PState sched j t) ->
       is_true (j \in @served_jobs_at Job PState arr_seq sched t)
```

## Lean

```lean
@Prosa.Analysis.Facts.Model.Scheduled.scheduled_at_implies_in_served_at : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobArrival Job]
  {PState : Prosa.Behavior.Schedule.ProcessorState Job}
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
    ∀ (sched : Prosa.Behavior.Schedule.schedule PState),
      Prosa.Behavior.Ready.jobs_come_from_arrival_sequence sched arr_seq →
        Prosa.Behavior.Ready.jobs_must_arrive_to_execute sched →
          Prosa.Model.Processor.PlatformProperties.ideal_progress_proc_model PState →
            ∀ (j : Job) (t : Prosa.Behavior.Time.instant),
              Prosa.Behavior.Service.scheduled_at sched j t = true →
                decide (j ∈ Prosa.Analysis.Definitions.Service.served_jobs_at arr_seq sched t) = true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_Scheduled_scheduled_at_implies_in_served_at
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
       Prosa_Model_Processor_PlatformProperties_ideal_progress_proc_model Job
         inst_3 PState ->
       forall (j : Job) (t : Prosa_Behavior_Time_instant),
       @eq Bool
         (Prosa_Behavior_Service_scheduled_at Job
            inst_3 PState sched j t)
         Bool_true ->
       @eq Bool
         (Decidable_decide
            (Membership_mem Job (List Job) (List_instMembership Job)
               (Prosa_Analysis_Definitions_Service_served_jobs_at Job
                  inst_3 PState arr_seq
                  sched t)
               j)
            (List_instDecidableMemOfLawfulBEq Job
               (instBEqOfDecidableEq Job
                  inst_3)
               (instLawfulBEq Job inst_3)
               j
               (Prosa_Analysis_Definitions_Service_served_jobs_at Job
                  inst_3 PState arr_seq
                  sched t)))
         Bool_true
```
