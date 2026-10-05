# `finish_time`

- Kind (Rocq): Definition
- Rocq: `prosa.analysis.definitions.finish_time.finish_time`
- Lean: `Prosa.Analysis.Definitions.FinishTime.finish_time`
- Certificate: `finish_time_correspondence`

## Official Rocq

```coq
finish_time :
forall {Job : JobType} {H : JobArrival Job} {H0 : JobCost Job} {PState : ProcessorState Job}
  (sched : @schedule Job PState) (j : Equality.sort Job) (R : nat),
is_true (@job_response_time_bound Job PState sched H0 H j R) -> instant

finish_time is not universe polymorphic
Arguments finish_time {Job H H0 PState} sched j R%nat_scope H_response_time_bounded
finish_time is transparent
Expands to: Constant prosa.analysis.definitions.finish_time.finish_time
Declared in library prosa.analysis.definitions.finish_time, line 45, characters 13-24
@finish_time
     : forall (Job : JobType) (H : JobArrival Job) (H0 : JobCost Job) (PState : ProcessorState Job)
         (sched : @schedule Job PState) (j : Equality.sort Job) (R : nat),
       is_true (@job_response_time_bound Job PState sched H0 H j R) -> instant
```

Body:

```coq
finish_time =
fun (Job : JobType) (H : JobArrival Job) (H0 : JobCost Job) (PState : ProcessorState Job)
  (sched : @schedule Job PState) (j : Equality.sort Job) (R : nat)
  (H_response_time_bounded : is_true (@job_response_time_bound Job PState sched H0 H j R)) =>
@ex_minn (@completed_by Job PState sched H0 j)
  (@finish_time.job_finishes Job H H0 PState sched j R H_response_time_bounded)
     : forall {Job : JobType} {H : JobArrival Job} {H0 : JobCost Job} {PState : ProcessorState Job}
         (sched : @schedule Job PState) (j : Equality.sort Job) (R : nat),
       is_true (@job_response_time_bound Job PState sched H0 H j R) -> instant

Arguments finish_time {Job H H0 PState} sched j R%nat_scope H_response_time_bounded
```

## Lean

```lean
@Prosa.Analysis.Definitions.FinishTime.finish_time : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [inst_1 : Prosa.Behavior.Job.JobArrival Job] →
      [inst_2 : Prosa.Behavior.Job.JobCost Job] →
        {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
          (sched : Prosa.Behavior.Schedule.schedule PState) →
            (j : Job) →
              (R : ℕ) → Prosa.Behavior.Service.job_response_time_bound sched j R = true → Prosa.Behavior.Time.instant
def Prosa.Analysis.Definitions.FinishTime.finish_time.{u_1, u_2, u_3} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [inst_1 : Prosa.Behavior.Job.JobArrival Job] →
      [inst_2 : Prosa.Behavior.Job.JobCost Job] →
        {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
          (sched : Prosa.Behavior.Schedule.schedule PState) →
            (j : Job) →
              (R : ℕ) → Prosa.Behavior.Service.job_response_time_bound sched j R = true → Prosa.Behavior.Time.instant :=
fun {Job} [DecidableEq Job] [Prosa.Behavior.Job.JobArrival Job] [Prosa.Behavior.Job.JobCost Job] {PState} sched j R
    H_response_time_bounded =>
  Nat.find ⋯
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Definitions_FinishTime_finish_time
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
       Prosa_Behavior_Time_instant
```

Body:

```coq
Prosa_Analysis_Definitions_FinishTime_finish_time@{u_1 u_2 u_3 Lean.u_1+1.0 Lean.max__u_1+1_u_2+2_u_3+2.0
Lean.u_2+1.0 Lean.u_3+1.0 Lean.u_1+2.0 Lean.u_3+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (inst_6 : Prosa_Behavior_Job_JobArrival
                                                                                Job
                                                                                inst_3)
  (inst_9 : Prosa_Behavior_Job_JobCost Job
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
                                  inst_6 j
                                  R)
                               Bool_true) =>
Nat_find
  (fun n : Nat =>
   Prosa_Behavior_Service_completed_by Job
     inst_3 PState sched
     inst_9 j n =
   Bool_true)
  (fun a : Nat =>
   instDecidableEqBool
     (Prosa_Behavior_Service_completed_by Job
        inst_3 PState sched
        inst_9 j a)
     Bool_true)
  (_private_Prosa_Analysis_Definitions_FinishTime0_Prosa_Analysis_Definitions_FinishTime_completion_witness
     Job inst_3
     inst_6
     inst_9 PState sched j R
     H_response_time_bounded)
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
       Prosa_Behavior_Time_instant

Arguments Prosa_Analysis_Definitions_FinishTime_finish_time Job
  inst_3
  inst_6
  inst_9 PState 
  sched j R%_Nat_scope H_response_time_bounded
```
