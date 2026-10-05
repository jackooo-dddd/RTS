# `earliest_finish_time`

- Kind (Rocq): Corollary
- Rocq: `prosa.analysis.definitions.finish_time.earliest_finish_time`
- Lean: `Prosa.Analysis.Definitions.FinishTime.earliest_finish_time`
- Certificate: `earliest_finish_time_statement_correspondence`

## Official Rocq

```coq
earliest_finish_time :
forall {Job : JobType} {H : JobArrival Job} {H0 : JobCost Job} {PState : ProcessorState Job}
  (sched : @schedule Job PState) (j : Equality.sort Job) (R : nat)
  (H_response_time_bounded : is_true (@job_response_time_bound Job PState sched H0 H j R)) 
  (t : instant),
is_true (@completed_by Job PState sched H0 j t) ->
is_true (@finish_time Job H H0 PState sched j R H_response_time_bounded <= t)

earliest_finish_time is not universe polymorphic
Arguments earliest_finish_time {Job H H0 PState} sched j R%nat_scope H_response_time_bounded t _
earliest_finish_time is opaque
Expands to: Constant prosa.analysis.definitions.finish_time.earliest_finish_time
Declared in library prosa.analysis.definitions.finish_time, line 58, characters 12-32
@earliest_finish_time
     : forall (Job : JobType) (H : JobArrival Job) (H0 : JobCost Job) (PState : ProcessorState Job)
         (sched : @schedule Job PState) (j : Equality.sort Job) (R : nat)
         (H_response_time_bounded : is_true (@job_response_time_bound Job PState sched H0 H j R))
         (t : instant),
       is_true (@completed_by Job PState sched H0 j t) ->
       is_true (@finish_time Job H H0 PState sched j R H_response_time_bounded <= t)
```

## Lean

```lean
@Prosa.Analysis.Definitions.FinishTime.earliest_finish_time : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobArrival Job] [inst_2 : Prosa.Behavior.Job.JobCost Job]
  {PState : Prosa.Behavior.Schedule.ProcessorState Job} (sched : Prosa.Behavior.Schedule.schedule PState) (j : Job)
  (R : ℕ) (H_response_time_bounded : Prosa.Behavior.Service.job_response_time_bound sched j R = true)
  (t : Prosa.Behavior.Time.instant),
  Prosa.Behavior.Service.completed_by sched j t = true →
    Prosa.Analysis.Definitions.FinishTime.finish_time sched j R H_response_time_bounded ≤ t
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Definitions_FinishTime_earliest_finish_time
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (inst_6 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_3)
         (inst_9 : 
          Prosa_Behavior_Job_JobCost Job
            inst_3)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState)
         (j : Job) (R : Nat)
         (H_response_time_bounded : @eq Bool
                                      (Prosa_Behavior_Service_job_response_time_bound Job
                                         inst_3
                                         PState sched
                                         inst_9
                                         inst_6
                                         j R)
                                      Bool_true)
         (t : Prosa_Behavior_Time_instant),
       @eq Bool
         (Prosa_Behavior_Service_completed_by Job
            inst_3 PState sched
            inst_9 j t)
         Bool_true ->
       LE_le_inst1 Prosa_Behavior_Time_instant instLENat
         (Prosa_Analysis_Definitions_FinishTime_finish_time Job
            inst_3
            inst_6
            inst_9 PState sched j R
            H_response_time_bounded)
         t
```
