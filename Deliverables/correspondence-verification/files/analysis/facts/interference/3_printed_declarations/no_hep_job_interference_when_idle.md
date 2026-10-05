# `no_hep_job_interference_when_idle`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.interference.no_hep_job_interference_when_idle`
- Lean: `Prosa.Analysis.Facts.Interference.no_hep_job_interference_when_idle`
- Certificate: `no_hep_job_interference_when_idle_correspondence`

## Official Rocq

```coq
no_hep_job_interference_when_idle :
forall {Job : JobType} {H1 : JobArrival Job} {PState : ProcessorState Job} (arr_seq : arrival_sequence Job),
@valid_arrival_sequence Job H1 arr_seq ->
forall sched : @schedule Job PState,
@jobs_come_from_arrival_sequence Job PState sched arr_seq ->
@jobs_must_arrive_to_execute Job H1 PState sched ->
forall {JLFP : JLFP_policy Job} (t : instant),
is_true (@is_idle Job PState arr_seq sched t) ->
forall j : Equality.sort Job, is_true (~~ @another_hep_job_interference Job PState arr_seq sched JLFP j t)

no_hep_job_interference_when_idle is not universe polymorphic
Arguments no_hep_job_interference_when_idle {Job H1 PState} arr_seq H_valid_arrival_sequence 
  sched H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute {JLFP} t 
  H_idle j
no_hep_job_interference_when_idle is opaque
Expands to: Constant prosa.analysis.facts.interference.no_hep_job_interference_when_idle
Declared in library prosa.analysis.facts.interference, line 186, characters 10-43
@no_hep_job_interference_when_idle
     : forall (Job : JobType) (H1 : JobArrival Job) (PState : ProcessorState Job)
         (arr_seq : arrival_sequence Job),
       @valid_arrival_sequence Job H1 arr_seq ->
       forall sched : @schedule Job PState,
       @jobs_come_from_arrival_sequence Job PState sched arr_seq ->
       @jobs_must_arrive_to_execute Job H1 PState sched ->
       forall (JLFP : JLFP_policy Job) (t : instant),
       is_true (@is_idle Job PState arr_seq sched t) ->
       forall j : Equality.sort Job,
       is_true (~~ @another_hep_job_interference Job PState arr_seq sched JLFP j t)
```

## Lean

```lean
@Prosa.Analysis.Facts.Interference.no_hep_job_interference_when_idle : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobArrival Job]
  {PState : Prosa.Behavior.Schedule.ProcessorState Job}
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
    ∀ (sched : Prosa.Behavior.Schedule.schedule PState),
      Prosa.Behavior.Ready.jobs_come_from_arrival_sequence sched arr_seq →
        Prosa.Behavior.Ready.jobs_must_arrive_to_execute sched →
          ∀ (JLFP : Prosa.Model.Priority.Definitions.JLFP_policy Job) (t : Prosa.Behavior.Time.instant),
            Prosa.Model.Schedule.Scheduled.is_idle arr_seq sched t = true →
              ∀ (j : Job),
                (!Prosa.Analysis.Definitions.Interference.another_hep_job_interference arr_seq sched j t) = true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Interference_no_hep_job_interference_when_idle
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
         (t : Prosa_Behavior_Time_instant),
       @eq Bool
         (Prosa_Model_Schedule_Scheduled_is_idle Job
            inst_3 PState arr_seq sched t)
         Bool_true ->
       forall j : Job,
       @eq Bool
         (Bool_not
            (Prosa_Analysis_Definitions_Interference_another_hep_job_interference Job
               inst_3 PState arr_seq sched
               JLFP j t))
         Bool_true
```
