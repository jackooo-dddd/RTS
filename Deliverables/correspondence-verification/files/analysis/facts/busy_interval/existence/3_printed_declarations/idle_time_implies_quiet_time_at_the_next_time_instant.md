# `idle_time_implies_quiet_time_at_the_next_time_instant`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.busy_interval.existence.idle_time_implies_quiet_time_at_the_next_time_instant`
- Lean: `Prosa.Analysis.Facts.BusyInterval.Existence.idle_time_implies_quiet_time_at_the_next_time_instant`
- Certificate: `idle_time_implies_quiet_time_at_the_next_time_instant_correspondence`

## Official Rocq

```coq
idle_time_implies_quiet_time_at_the_next_time_instant :
forall {Job : JobType} {Arrival : JobArrival Job} {Cost : JobCost Job} (arr_seq : arrival_sequence Job),
@valid_arrival_sequence Job Arrival arr_seq ->
forall {PState : ProcessorState Job} (sched : @schedule Job PState),
@jobs_come_from_arrival_sequence Job PState sched arr_seq ->
@jobs_must_arrive_to_execute Job Arrival PState sched ->
forall {JLFP : JLFP_policy Job} {H0 : @JobReady Job PState Cost Arrival},
@work_bearing_readiness Job Arrival Cost PState H0 arr_seq sched JLFP ->
forall j : Equality.sort Job,
@work_conserving Job Arrival Cost PState H0 arr_seq sched ->
forall t : instant,
is_true (@is_idle Job PState arr_seq sched t) ->

idle_time_implies_quiet_time_at_the_next_time_instant is not universe polymorphic
Arguments idle_time_implies_quiet_time_at_the_next_time_instant {Job Arrival Cost} 
  arr_seq H_valid_arrival_time {PState} sched H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
  {JLFP H0} H_job_ready j H_work_conserving t _ j_hp _ _ _
idle_time_implies_quiet_time_at_the_next_time_instant is opaque
Expands to: Constant
            prosa.analysis.facts.busy_interval.existence.idle_time_implies_quiet_time_at_the_next_time_instant
Declared in library prosa.analysis.facts.busy_interval.existence, line 143, characters 10-63
@idle_time_implies_quiet_time_at_the_next_time_instant
     : forall (Job : JobType) (Arrival : JobArrival Job) (Cost : JobCost Job)
         (arr_seq : arrival_sequence Job),
       @valid_arrival_sequence Job Arrival arr_seq ->
       forall (PState : ProcessorState Job) (sched : @schedule Job PState),
       @jobs_come_from_arrival_sequence Job PState sched arr_seq ->
       @jobs_must_arrive_to_execute Job Arrival PState sched ->
       forall (JLFP : JLFP_policy Job) (H0 : @JobReady Job PState Cost Arrival),
       @work_bearing_readiness Job Arrival Cost PState H0 arr_seq sched JLFP ->
       forall j : Equality.sort Job,
       @work_conserving Job Arrival Cost PState H0 arr_seq sched ->
       forall t : instant,
       is_true (@is_idle Job PState arr_seq sched t) ->
       @quiet_time Job Arrival Cost PState arr_seq sched JLFP j t.+1
```

## Lean

```lean
@Prosa.Analysis.Facts.BusyInterval.Existence.idle_time_implies_quiet_time_at_the_next_time_instant : ∀
  {Job : Prosa.Behavior.Job.JobType} [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobArrival Job]
  [inst_2 : Prosa.Behavior.Job.JobCost Job] (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
    ∀ {PState : Prosa.Behavior.Schedule.ProcessorState Job} (sched : Prosa.Behavior.Schedule.schedule PState),
      Prosa.Behavior.Ready.jobs_come_from_arrival_sequence sched arr_seq →
        Prosa.Behavior.Ready.jobs_must_arrive_to_execute sched →
          ∀ (JLFP : Prosa.Model.Priority.Definitions.JLFP_policy Job)
            [inst_3 : Prosa.Behavior.Ready.JobReady Job PState],
            Prosa.Analysis.Definitions.WorkBearingReadiness.work_bearing_readiness arr_seq sched →
              ∀ (j : Job),
                Prosa.Model.Schedule.WorkConserving.work_conserving arr_seq sched →
                  ∀ (t : Prosa.Behavior.Time.instant),
                    Prosa.Model.Schedule.Scheduled.is_idle arr_seq sched t = true →
                      Prosa.Analysis.Definitions.BusyInterval.Classical.quiet_time arr_seq sched j (t + 1)
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_BusyInterval_Existence_idle_time_implies_quiet_time_at_the_next_time_instant
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (inst_6 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_3)
         (inst_9 : 
          Prosa_Behavior_Job_JobCost Job
            inst_3)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_3),
       Prosa_Behavior_Arrival_sequence_valid_arrival_sequence Job
         inst_3
         inst_6 arr_seq ->
       forall
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState),
       Prosa_Behavior_Ready_jobs_come_from_arrival_sequence Job
         inst_3 PState sched
         arr_seq ->
       Prosa_Behavior_Ready_jobs_must_arrive_to_execute Job
         inst_3
         inst_6 PState sched ->
       forall
         (JLFP : Prosa_Model_Priority_Definitions_JLFP_policy Job
                   inst_3)
         (inst_34 : 
          Prosa_Behavior_Ready_JobReady Job
            inst_3 PState
            inst_9
            inst_6),
       Prosa_Analysis_Definitions_WorkBearingReadiness_work_bearing_readiness Job
         inst_3
         inst_6
         inst_9 PState
         inst_34 arr_seq sched JLFP ->
       forall j : Job,
       Prosa_Model_Schedule_WorkConserving_work_conserving Job
         inst_3
         inst_6
         inst_9 PState
         inst_34 arr_seq sched ->
       forall t : Prosa_Behavior_Time_instant,
       @eq Bool
         (Prosa_Model_Schedule_Scheduled_is_idle Job
            inst_3 PState arr_seq
            sched t)
         Bool_true ->
       Prosa_Analysis_Definitions_BusyInterval_Classical_quiet_time Job
         inst_3
         inst_6
         inst_9 PState arr_seq
         sched JLFP j
         (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant
            (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) t
            (OfNat_ofNat_inst1 Prosa_Behavior_Time_instant 1 (instOfNatNat 1)))
```
