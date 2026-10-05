# `job_response_time_bound`

- Kind (Rocq): Definition
- Rocq: `prosa.behavior.service.job_response_time_bound`
- Lean: `Prosa.Behavior.Service.job_response_time_bound`
- Certificate: ``

## Official Rocq

```coq
job_response_time_bound :
forall {Job : JobType} {PState : ProcessorState Job},
@schedule Job PState -> JobCost Job -> JobArrival Job -> Equality.sort Job -> duration -> bool

job_response_time_bound is not universe polymorphic
Arguments job_response_time_bound {Job PState} sched {H H1} j R
job_response_time_bound is transparent
Expands to: Constant prosa.behavior.service.job_response_time_bound
Declared in library prosa.behavior.service, line 52, characters 13-36
@job_response_time_bound
     : forall (Job : JobType) (PState : ProcessorState Job),
       @schedule Job PState -> JobCost Job -> JobArrival Job -> Equality.sort Job -> duration -> bool
```

Body:

```coq
job_response_time_bound =
fun (Job : JobType) (PState : ProcessorState Job) (sched : @schedule Job PState) 
  (H : JobCost Job) (H1 : JobArrival Job) (j : Equality.sort Job) (R : duration) =>
@completed_by Job PState sched H j (@job_arrival Job H1 j + R)
     : forall {Job : JobType} {PState : ProcessorState Job},
       @schedule Job PState -> JobCost Job -> JobArrival Job -> Equality.sort Job -> duration -> bool

Arguments job_response_time_bound {Job PState} sched {H H1} j R
```

## Lean

```lean
@Prosa.Behavior.Service.job_response_time_bound : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
      Prosa.Behavior.Schedule.schedule PState →
        [Prosa.Behavior.Job.JobCost Job] →
          [Prosa.Behavior.Job.JobArrival Job] → Job → Prosa.Behavior.Time.duration → Bool
def Prosa.Behavior.Service.job_response_time_bound.{u_1, u_2, u_3} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
      Prosa.Behavior.Schedule.schedule PState →
        [Prosa.Behavior.Job.JobCost Job] →
          [Prosa.Behavior.Job.JobArrival Job] → Job → Prosa.Behavior.Time.duration → Bool :=
fun {Job} [DecidableEq Job] {PState} sched [Prosa.Behavior.Job.JobCost Job] [Prosa.Behavior.Job.JobArrival Job] j R =>
  Prosa.Behavior.Service.completed_by sched j (Prosa.Behavior.Job.job_arrival j + R)
```

## Lean, imported into Rocq

```coq
ImportedService.Prosa_Behavior_Service_job_response_time_bound
     : forall (Job : ImportedService.Prosa_Behavior_Job_JobType)
         (inst_3 : ImportedService.DecidableEq Job)
         (PState : ImportedService.Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3),
       ImportedService.Prosa_Behavior_Schedule_schedule Job
         inst_3 PState ->
       ImportedService.Prosa_Behavior_Job_JobCost Job
         inst_3 ->
       ImportedService.Prosa_Behavior_Job_JobArrival Job
         inst_3 ->
       Job -> ImportedService.Prosa_Behavior_Time_duration -> ImportedService.Bool
```

Body:

```coq
ImportedService.Prosa_Behavior_Service_job_response_time_bound@{u_1 u_2 u_3 Lean.u_1+1.0
Lean.max__u_1+1_u_2+2_u_3+2.0 Lean.u_2+1.0 Lean.u_3+1.0 Lean.u_1+2.0 Lean.u_3+2.0} =
fun (Job : ImportedService.Prosa_Behavior_Job_JobType)
  (inst_9 : 
   ImportedService.DecidableEq Job)
  (PState : ImportedService.Prosa_Behavior_Schedule_ProcessorState Job
              inst_9)
  (sched : ImportedService.Prosa_Behavior_Schedule_schedule Job
             inst_9
             PState)
  (inst_16 : 
   ImportedService.Prosa_Behavior_Job_JobCost Job
     inst_9)
  (inst_19 : 
   ImportedService.Prosa_Behavior_Job_JobArrival Job
     inst_9)
  (j : Job) (R : ImportedService.Prosa_Behavior_Time_duration) =>
ImportedService.Prosa_Validation_ServiceInterface_completedByProjection Job
  inst_9
  PState sched
  inst_16 j
  (ImportedService.HAdd_hAdd_inst7 ImportedService.Prosa_Behavior_Time_instant
     ImportedService.Prosa_Behavior_Time_duration ImportedService.Prosa_Behavior_Time_instant
     (ImportedService.instHAdd_inst1 ImportedService.Prosa_Behavior_Time_instant ImportedService.instAddNat)
     (ImportedService.Prosa_Behavior_Job_JobArrival_job_arrival Job
        inst_9
        inst_19
        j)
     R)
     : forall (Job : ImportedService.Prosa_Behavior_Job_JobType)
         (inst_3 : ImportedService.DecidableEq Job)
         (PState : ImportedService.Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3),
       ImportedService.Prosa_Behavior_Schedule_schedule Job
         inst_3 PState ->
       ImportedService.Prosa_Behavior_Job_JobCost Job
         inst_3 ->
       ImportedService.Prosa_Behavior_Job_JobArrival Job
         inst_3 ->
       Job -> ImportedService.Prosa_Behavior_Time_duration -> ImportedService.Bool

Arguments ImportedService.Prosa_Behavior_Service_job_response_time_bound Job
  inst_3 PState sched
  inst_10
  inst_16 j R
```
