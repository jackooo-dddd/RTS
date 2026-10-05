# `pending_job_not_idle`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.busy_interval.carry_in.pending_job_not_idle`
- Lean: `Prosa.Analysis.Facts.BusyInterval.CarryIn.pending_job_not_idle`
- Certificate: `pending_job_not_idle_correspondence`

## Official Rocq

```coq
pending_job_not_idle :
forall {Job : JobType} {H1 : JobArrival Job} {H2 : JobCost Job} (arr_seq : arrival_sequence Job),
@valid_arrival_sequence Job H1 arr_seq ->
forall {PState : ProcessorState Job} (sched : @schedule Job PState),
@jobs_come_from_arrival_sequence Job PState sched arr_seq ->
@jobs_must_arrive_to_execute Job H1 PState sched ->
forall {JLFP : JLFP_policy Job} {JobReady0 : @JobReady Job PState H2 H1},
@work_bearing_readiness Job H1 H2 PState JobReady0 arr_seq sched JLFP ->
@work_conserving Job H1 H2 PState JobReady0 arr_seq sched ->
forall (j : Equality.sort Job) (t : instant),
@arrives_in Job arr_seq j ->
is_true (@pending Job PState sched H2 H1 j t) -> ~ is_true (@is_idle Job PState arr_seq sched t)

pending_job_not_idle is not universe polymorphic
Arguments pending_job_not_idle {Job H1 H2} arr_seq H_valid_arr_seq {PState} sched
  H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute {JLFP JobReady0} 
  H_job_ready H_work_conserving j t _ _ _
pending_job_not_idle is opaque
Expands to: Constant prosa.analysis.facts.busy_interval.carry_in.pending_job_not_idle
Declared in library prosa.analysis.facts.busy_interval.carry_in, line 70, characters 8-28
@pending_job_not_idle
     : forall (Job : JobType) (H1 : JobArrival Job) (H2 : JobCost Job) (arr_seq : arrival_sequence Job),
       @valid_arrival_sequence Job H1 arr_seq ->
       forall (PState : ProcessorState Job) (sched : @schedule Job PState),
       @jobs_come_from_arrival_sequence Job PState sched arr_seq ->
       @jobs_must_arrive_to_execute Job H1 PState sched ->
       forall (JLFP : JLFP_policy Job) (JobReady0 : @JobReady Job PState H2 H1),
       @work_bearing_readiness Job H1 H2 PState JobReady0 arr_seq sched JLFP ->
       @work_conserving Job H1 H2 PState JobReady0 arr_seq sched ->
       forall (j : Equality.sort Job) (t : instant),
       @arrives_in Job arr_seq j ->
       is_true (@pending Job PState sched H2 H1 j t) -> ~ is_true (@is_idle Job PState arr_seq sched t)
```

## Lean

```lean
@Prosa.Analysis.Facts.BusyInterval.CarryIn.pending_job_not_idle : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobArrival Job] [inst_2 : Prosa.Behavior.Job.JobCost Job]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
    ∀ {PState : Prosa.Behavior.Schedule.ProcessorState Job} (sched : Prosa.Behavior.Schedule.schedule PState),
      Prosa.Behavior.Ready.jobs_come_from_arrival_sequence sched arr_seq →
        Prosa.Behavior.Ready.jobs_must_arrive_to_execute sched →
          ∀ (JLFP : Prosa.Model.Priority.Definitions.JLFP_policy Job)
            [inst_3 : Prosa.Behavior.Ready.JobReady Job PState],
            Prosa.Analysis.Definitions.WorkBearingReadiness.work_bearing_readiness arr_seq sched →
              Prosa.Model.Schedule.WorkConserving.work_conserving arr_seq sched →
                ∀ (j : Job) (t : Prosa.Behavior.Time.instant),
                  Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j →
                    Prosa.Behavior.Service.pending sched j t = true →
                      ¬Prosa.Model.Schedule.Scheduled.is_idle arr_seq sched t = true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_BusyInterval_CarryIn_pending_job_not_idle
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
         inst_3 PState sched arr_seq ->
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
       Prosa_Model_Schedule_WorkConserving_work_conserving Job
         inst_3
         inst_6
         inst_9 PState
         inst_34 arr_seq sched ->
       forall (j : Job) (t : Prosa_Behavior_Time_instant),
       Prosa_Behavior_Arrival_sequence_arrives_in Job
         inst_3 arr_seq j ->
       @eq Bool
         (Prosa_Behavior_Service_pending Job
            inst_3 PState sched
            inst_9
            inst_6 j t)
         Bool_true ->
       Not
         (@eq Bool
            (Prosa_Model_Schedule_Scheduled_is_idle Job
               inst_3 PState arr_seq
               sched t)
            Bool_true)
```
