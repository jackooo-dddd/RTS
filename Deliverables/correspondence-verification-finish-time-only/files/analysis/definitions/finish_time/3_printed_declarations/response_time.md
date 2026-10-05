# `response_time`

- Kind (Rocq): Definition
- Rocq: `prosa.analysis.definitions.finish_time.response_time`
- Lean: `Prosa.Analysis.Definitions.FinishTime.response_time`
- Certificate: `response_time_correspondence` in [`FinishTimeCorrespondence.v`](../4_correspondence/FinishTimeCorrespondence.v)

## Official Rocq

```coq
response_time :
forall {Job : JobType} {H : JobArrival Job} {H0 : JobCost Job} {PState : ProcessorState Job}
  (sched : @schedule Job PState) (j : Equality.sort Job) (R : nat),
is_true (@job_response_time_bound Job PState sched H0 H j R) -> duration

response_time is not universe polymorphic
Arguments response_time {Job H H0 PState} sched j R%_nat_scope H_response_time_bounded
response_time is transparent
Expands to: Constant prosa.analysis.definitions.finish_time.response_time
Declared in library prosa.analysis.definitions.finish_time, line 81, characters 13-26
@response_time
     : forall (Job : JobType) (H : JobArrival Job) (H0 : JobCost Job) (PState : ProcessorState Job)
         (sched : @schedule Job PState) (j : Equality.sort Job) (R : nat),
       is_true (@job_response_time_bound Job PState sched H0 H j R) -> duration
```

Body:

```coq
response_time =
fun (Job : JobType) (H : JobArrival Job) (H0 : JobCost Job) (PState : ProcessorState Job)
  (sched : @schedule Job PState) (j : Equality.sort Job) (R : nat)
  (H_response_time_bounded : is_true (@job_response_time_bound Job PState sched H0 H j R)) =>
@finish_time Job H H0 PState sched j R H_response_time_bounded - @job_arrival Job H j
     : forall {Job : JobType} {H : JobArrival Job} {H0 : JobCost Job} {PState : ProcessorState Job}
         (sched : @schedule Job PState) (j : Equality.sort Job) (R : nat),
       is_true (@job_response_time_bound Job PState sched H0 H j R) -> duration

Arguments response_time {Job H H0 PState} sched j R%_nat_scope H_response_time_bounded
```

## Lean

```lean
@response_time : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [inst_1 : Prosa.Behavior.Job.JobArrival Job] →
      [inst_2 : Prosa.Behavior.Job.JobCost Job] →
        {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
          (sched : Prosa.Behavior.Schedule.schedule PState) →
            (j : Job) →
              (R : ℕ) → Prosa.Behavior.Service.job_response_time_bound sched j R = true → Prosa.Behavior.Time.duration
```

Body:

```lean
def Prosa.Analysis.Definitions.FinishTime.response_time.{u_1, u_2, u_3} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [inst_1 : Prosa.Behavior.Job.JobArrival Job] →
      [inst_2 : Prosa.Behavior.Job.JobCost Job] →
        {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
          (sched : Prosa.Behavior.Schedule.schedule PState) →
            (j : Job) →
              (R : ℕ) →
                Prosa.Behavior.Service.job_response_time_bound sched j R = true → Prosa.Behavior.Time.duration :=
fun {Job : Prosa.Behavior.Job.JobType} [DecidableEq Job] [Prosa.Behavior.Job.JobArrival Job]
    [Prosa.Behavior.Job.JobCost Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job}
    (sched : Prosa.Behavior.Schedule.schedule PState) (j : Job) (R : ℕ)
    (H_response_time_bounded : Prosa.Behavior.Service.job_response_time_bound sched j R = true) =>
  finish_time sched j R H_response_time_bounded - Prosa.Behavior.Job.job_arrival j
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Definitions_FinishTime_response_time
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
         (j : Job) (R : Nat),
       @eq Bool
         (Prosa_Behavior_Service_job_response_time_bound Job
            inst_3 PState sched
            inst_9
            inst_6 j R)
         Bool_true ->
       Prosa_Behavior_Time_duration
```

Body:

```coq
Prosa_Analysis_Definitions_FinishTime_response_time@{u_1 u_2 u_3 Lean.u_1+1.0 Lean.max__u_1+1_u_2+2_u_3+2.0
Lean.u_2+1.0 Lean.u_3+1.0 Lean.u_1+2.0 Lean.u_3+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (inst_6 : Prosa_Behavior_Job_JobArrival
                                                                                Job
                                                                                inst_3)
  (inst_9 : Prosa_Behavior_Job_JobCost
                                                                                Job
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
                               Bool_true) =>
HSub_hSub_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant
  (instHSub_inst1 Prosa_Behavior_Time_instant instSubNat)
  (Prosa_Analysis_Definitions_FinishTime_finish_time Job
     inst_3
     inst_6
     inst_9 PState sched j R
     H_response_time_bounded)
  (Prosa_Behavior_Job_JobArrival_job_arrival Job
     inst_3
     inst_6 j)
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
         (j : Job) (R : Nat),
       @eq Bool
         (Prosa_Behavior_Service_job_response_time_bound Job
            inst_3 PState sched
            inst_9
            inst_6 j R)
         Bool_true ->
       Prosa_Behavior_Time_duration

Arguments Prosa_Analysis_Definitions_FinishTime_response_time Job
  inst_3
  inst_6
  inst_9 PState 
  sched j R%_Nat_scope H_response_time_bounded
```
