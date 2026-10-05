# `completetion_time_is_preemption_time`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.completes_at.completetion_time_is_preemption_time`
- Lean: `Prosa.Analysis.Facts.CompletesAt.completetion_time_is_preemption_time`
- Certificate: `completetion_time_is_preemption_time_correspondence`

## Official Rocq

```coq
completetion_time_is_preemption_time :
forall {Job : JobType} {H : JobArrival Job} {H0 : JobCost Job} {PState : ProcessorState Job},
@uniprocessor_model Job PState ->
forall arr_seq : arrival_sequence Job,
@valid_arrival_sequence Job H arr_seq ->
forall sched : @schedule Job PState,
@jobs_come_from_arrival_sequence Job PState sched arr_seq ->
@jobs_must_arrive_to_execute Job H PState sched ->
@completed_jobs_dont_execute Job PState sched H0 ->
forall {H2 : JobPreemptable Job},
@valid_preemption_model Job H0 H2 PState arr_seq sched ->
forall (j : Equality.sort Job) (t : instant),
is_true (@completes_at Job PState sched H0 j t) -> is_true (@preemption_time Job H2 arr_seq PState sched t)

completetion_time_is_preemption_time is not universe polymorphic
Arguments completetion_time_is_preemption_time {Job H H0 PState} H_uniprocessor_proc_model 
  arr_seq H_valid_arrival_sequence sched H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
  H_completed_jobs_dont_execute {H2} H_valid_preemption_model j t _
completetion_time_is_preemption_time is opaque
Expands to: Constant prosa.analysis.facts.completes_at.completetion_time_is_preemption_time
Declared in library prosa.analysis.facts.completes_at, line 86, characters 8-44
@completetion_time_is_preemption_time
     : forall (Job : JobType) (H : JobArrival Job) (H0 : JobCost Job) (PState : ProcessorState Job),
       @uniprocessor_model Job PState ->
       forall arr_seq : arrival_sequence Job,
       @valid_arrival_sequence Job H arr_seq ->
       forall sched : @schedule Job PState,
       @jobs_come_from_arrival_sequence Job PState sched arr_seq ->
       @jobs_must_arrive_to_execute Job H PState sched ->
       @completed_jobs_dont_execute Job PState sched H0 ->
       forall H2 : JobPreemptable Job,
       @valid_preemption_model Job H0 H2 PState arr_seq sched ->
       forall (j : Equality.sort Job) (t : instant),
       is_true (@completes_at Job PState sched H0 j t) ->
       is_true (@preemption_time Job H2 arr_seq PState sched t)
```

## Lean

```lean
@Prosa.Analysis.Facts.CompletesAt.completetion_time_is_preemption_time : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobArrival Job] [inst_2 : Prosa.Behavior.Job.JobCost Job]
  {PState : Prosa.Behavior.Schedule.ProcessorState Job},
  Prosa.Model.Processor.PlatformProperties.uniprocessor_model PState →
    ∀ (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
      Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
        ∀ (sched : Prosa.Behavior.Schedule.schedule PState),
          Prosa.Behavior.Ready.jobs_come_from_arrival_sequence sched arr_seq →
            Prosa.Behavior.Ready.jobs_must_arrive_to_execute sched →
              Prosa.Behavior.Ready.completed_jobs_dont_execute sched →
                ∀ [inst_3 : Prosa.Model.Preemption.Parameter.JobPreemptable Job],
                  Prosa.Model.Preemption.Parameter.valid_preemption_model arr_seq sched →
                    ∀ (j : Job) (t : Prosa.Behavior.Time.instant),
                      Prosa.Behavior.Service.completes_at sched j t = true →
                        Prosa.Model.Schedule.PreemptionTime.preemption_time arr_seq sched t = true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_CompletesAt_completetion_time_is_preemption_time
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
         arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                     inst_3,
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
       Prosa_Behavior_Ready_completed_jobs_dont_execute Job
         inst_3 PState sched
         inst_9 ->
       forall
         inst_44 : 
          Prosa_Model_Preemption_Parameter_JobPreemptable Job
            inst_3,
       Prosa_Model_Preemption_Parameter_valid_preemption_model Job
         inst_3
         inst_9
         inst_44 PState arr_seq sched ->
       forall (j : Job) (t : Prosa_Behavior_Time_instant),
       @eq Bool
         (Prosa_Behavior_Service_completes_at Job
            inst_3 PState sched
            inst_9 j t)
         Bool_true ->
       @eq Bool
         (Prosa_Model_Schedule_PreemptionTime_preemption_time Job
            inst_3
            inst_44 arr_seq PState sched t)
         Bool_true
```
