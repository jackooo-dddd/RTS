# `no_priority_inversion_when_idle`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.priority.inversion.no_priority_inversion_when_idle`
- Lean: `Prosa.Analysis.Facts.Priority.Inversion.no_priority_inversion_when_idle`
- Certificate: `no_priority_inversion_when_idle_correspondence`

## Official Rocq

```coq
no_priority_inversion_when_idle :
forall {Job : JobType} {H1 : JobArrival Job} {PState : ProcessorState Job} (arr_seq : arrival_sequence Job),
@valid_arrival_sequence Job H1 arr_seq ->
forall sched : @schedule Job PState,
@jobs_come_from_arrival_sequence Job PState sched arr_seq ->
@jobs_must_arrive_to_execute Job H1 PState sched ->
forall {JLFP : JLFP_policy Job} (j : Equality.sort Job) (t : instant),
is_true (@is_idle Job PState arr_seq sched t) ->
is_true (~~ @priority_inversion Job PState arr_seq sched JLFP j t)

no_priority_inversion_when_idle is not universe polymorphic
Arguments no_priority_inversion_when_idle {Job H1 PState} arr_seq H_valid_arrival_sequence 
  sched H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute {JLFP} j 
  t _
no_priority_inversion_when_idle is opaque
Expands to: Constant prosa.analysis.facts.priority.inversion.no_priority_inversion_when_idle
Declared in library prosa.analysis.facts.priority.inversion, line 65, characters 8-39
@no_priority_inversion_when_idle
     : forall (Job : JobType) (H1 : JobArrival Job) (PState : ProcessorState Job)
         (arr_seq : arrival_sequence Job),
       @valid_arrival_sequence Job H1 arr_seq ->
       forall sched : @schedule Job PState,
       @jobs_come_from_arrival_sequence Job PState sched arr_seq ->
       @jobs_must_arrive_to_execute Job H1 PState sched ->
       forall (JLFP : JLFP_policy Job) (j : Equality.sort Job) (t : instant),
       is_true (@is_idle Job PState arr_seq sched t) ->
       is_true (~~ @priority_inversion Job PState arr_seq sched JLFP j t)
```

## Lean

```lean
@Prosa.Analysis.Facts.Priority.Inversion.no_priority_inversion_when_idle : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobArrival Job]
  {PState : Prosa.Behavior.Schedule.ProcessorState Job}
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
    ∀ (sched : Prosa.Behavior.Schedule.schedule PState),
      Prosa.Behavior.Ready.jobs_come_from_arrival_sequence sched arr_seq →
        Prosa.Behavior.Ready.jobs_must_arrive_to_execute sched →
          ∀ [JLFP : Prosa.Model.Priority.Definitions.JLFP_policy Job] (j : Job) (t : Prosa.Behavior.Time.instant),
            Prosa.Model.Schedule.Scheduled.is_idle arr_seq sched t = true →
              (!Prosa.Analysis.Definitions.PriorityInversion.priority_inversion arr_seq sched j t) = true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Priority_Inversion_no_priority_inversion_when_idle
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
       forall
         (JLFP : Prosa_Model_Priority_Definitions_JLFP_policy Job
                   inst_3)
         (j : Job) (t : Prosa_Behavior_Time_instant),
       @eq Bool
         (Prosa_Model_Schedule_Scheduled_is_idle Job
            inst_3 PState arr_seq sched
            t)
         Bool_true ->
       @eq Bool
         (Bool_not
            (Prosa_Analysis_Definitions_PriorityInversion_priority_inversion Job
               inst_3 PState arr_seq
               sched JLFP j t))
         Bool_true
```
