# `job_response_time_exceeds`

- Kind (Rocq): Definition
- Rocq: `prosa.analysis.definitions.job_response_time.job_response_time_exceeds`
- Lean: `Prosa.Analysis.Definitions.JobResponseTime.job_response_time_exceeds`
- Certificate: `job_response_time_exceeds_correspondence`

## Official Rocq

```coq
job_response_time_exceeds :
forall {Job : JobType},
JobCost Job ->
JobArrival Job ->
forall {PState : ProcessorState Job}, @schedule Job PState -> Equality.sort Job -> duration -> bool

job_response_time_exceeds is not universe polymorphic
Arguments job_response_time_exceeds {Job H H0 PState} sched j x
job_response_time_exceeds is transparent
Expands to: Constant prosa.analysis.definitions.job_response_time.job_response_time_exceeds
Declared in library prosa.analysis.definitions.job_response_time, line 20, characters 13-38
@job_response_time_exceeds
     : forall Job : JobType,
       JobCost Job ->
       JobArrival Job ->
       forall PState : ProcessorState Job, @schedule Job PState -> Equality.sort Job -> duration -> bool
```

Body:

```coq
job_response_time_exceeds =
fun (Job : JobType) (H : JobCost Job) (H0 : JobArrival Job) (PState : ProcessorState Job)
  (sched : @schedule Job PState) (j : Equality.sort Job) (x : duration) =>
~~ @completed_by Job PState sched H j (@job_arrival Job H0 j + x)
     : forall {Job : JobType},
       JobCost Job ->
       JobArrival Job ->
       forall {PState : ProcessorState Job}, @schedule Job PState -> Equality.sort Job -> duration -> bool

Arguments job_response_time_exceeds {Job H H0 PState} sched j x
```

## Lean

```lean
@Prosa.Analysis.Definitions.JobResponseTime.job_response_time_exceeds : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [Prosa.Behavior.Job.JobCost Job] →
      [Prosa.Behavior.Job.JobArrival Job] →
        {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
          Prosa.Behavior.Schedule.schedule PState → Job → Prosa.Behavior.Time.duration → Bool
def Prosa.Analysis.Definitions.JobResponseTime.job_response_time_exceeds.{u_1, u_2, u_3} : {Job :
    Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [Prosa.Behavior.Job.JobCost Job] →
      [Prosa.Behavior.Job.JobArrival Job] →
        {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
          Prosa.Behavior.Schedule.schedule PState → Job → Prosa.Behavior.Time.duration → Bool :=
fun {Job} [DecidableEq Job] [Prosa.Behavior.Job.JobCost Job] [Prosa.Behavior.Job.JobArrival Job] {PState} sched j x =>
  !Prosa.Behavior.Service.completed_by sched j (Prosa.Behavior.Job.job_arrival j + x)
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Definitions_JobResponseTime_job_response_time_exceeds
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Behavior_Job_JobCost Job
         inst_3 ->
       Prosa_Behavior_Job_JobArrival Job
         inst_3 ->
       forall
         PState : Prosa_Behavior_Schedule_ProcessorState Job
                    inst_3,
       Prosa_Behavior_Schedule_schedule Job
         inst_3 PState ->
       Job -> Prosa_Behavior_Time_duration -> Bool
```

Body:

```coq
Prosa_Analysis_Definitions_JobResponseTime_job_response_time_exceeds@{u_1 u_2 u_3 Lean.u_1+1.0
Lean.max__u_1+1_u_2+2_u_3+2.0 Lean.u_2+1.0 Lean.u_3+1.0 Lean.u_1+2.0 Lean.u_3+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (inst_6 : 
   Prosa_Behavior_Job_JobCost Job
     inst_3)
  (inst_9 : 
   Prosa_Behavior_Job_JobArrival Job
     inst_3)
  (PState : Prosa_Behavior_Schedule_ProcessorState Job
              inst_3)
  (sched : Prosa_Behavior_Schedule_schedule Job
             inst_3 PState)
  (j : Job) (x : Prosa_Behavior_Time_duration) =>
Bool_not
  (Prosa_Behavior_Service_completed_by Job
     inst_3 PState sched
     inst_6 j
     (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_duration Prosa_Behavior_Time_instant
        (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat)
        (Prosa_Behavior_Job_JobArrival_job_arrival Job
           inst_3
           inst_9 j)
        x))
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Behavior_Job_JobCost Job
         inst_3 ->
       Prosa_Behavior_Job_JobArrival Job
         inst_3 ->
       forall
         PState : Prosa_Behavior_Schedule_ProcessorState Job
                    inst_3,
       Prosa_Behavior_Schedule_schedule Job
         inst_3 PState ->
       Job -> Prosa_Behavior_Time_duration -> Bool

Arguments Prosa_Analysis_Definitions_JobResponseTime_job_response_time_exceeds Job
  inst_3
  inst_6
  inst_9 
  PState sched j x
```
