# `job_meets_deadline`

- Kind (Rocq): Definition
- Rocq: `prosa.behavior.service.job_meets_deadline`
- Lean: `Prosa.Behavior.Service.job_meets_deadline`
- Certificate: ``

## Official Rocq

```coq
job_meets_deadline :
forall {Job : JobType} {PState : ProcessorState Job},
@schedule Job PState -> JobCost Job -> JobDeadline Job -> Equality.sort Job -> bool

job_meets_deadline is not universe polymorphic
Arguments job_meets_deadline {Job PState} sched {H H0} j
job_meets_deadline is transparent
Expands to: Constant prosa.behavior.service.job_meets_deadline
Declared in library prosa.behavior.service, line 56, characters 13-31
@job_meets_deadline
     : forall (Job : JobType) (PState : ProcessorState Job),
       @schedule Job PState -> JobCost Job -> JobDeadline Job -> Equality.sort Job -> bool
```

Body:

```coq
job_meets_deadline =
fun (Job : JobType) (PState : ProcessorState Job) (sched : @schedule Job PState) 
  (H : JobCost Job) (H0 : JobDeadline Job) (j : Equality.sort Job) =>
@completed_by Job PState sched H j (@job_deadline Job H0 j)
     : forall {Job : JobType} {PState : ProcessorState Job},
       @schedule Job PState -> JobCost Job -> JobDeadline Job -> Equality.sort Job -> bool

Arguments job_meets_deadline {Job PState} sched {H H0} j
```

## Lean

```lean
@Prosa.Behavior.Service.job_meets_deadline : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
      Prosa.Behavior.Schedule.schedule PState →
        [Prosa.Behavior.Job.JobCost Job] → [Prosa.Behavior.Job.JobDeadline Job] → Job → Bool
def Prosa.Behavior.Service.job_meets_deadline.{u_1, u_2, u_3} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
      Prosa.Behavior.Schedule.schedule PState →
        [Prosa.Behavior.Job.JobCost Job] → [Prosa.Behavior.Job.JobDeadline Job] → Job → Bool :=
fun {Job} [DecidableEq Job] {PState} sched [Prosa.Behavior.Job.JobCost Job] [Prosa.Behavior.Job.JobDeadline Job] j =>
  Prosa.Behavior.Service.completed_by sched j (Prosa.Behavior.Job.job_deadline j)
```

## Lean, imported into Rocq

```coq
ImportedService.Prosa_Behavior_Service_job_meets_deadline
     : forall (Job : ImportedService.Prosa_Behavior_Job_JobType)
         (inst_3 : ImportedService.DecidableEq Job)
         (PState : ImportedService.Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3),
       ImportedService.Prosa_Behavior_Schedule_schedule Job
         inst_3 PState ->
       ImportedService.Prosa_Behavior_Job_JobCost Job
         inst_3 ->
       ImportedService.Prosa_Behavior_Job_JobDeadline Job
         inst_3 ->
       Job -> ImportedService.Bool
```

Body:

```coq
ImportedService.Prosa_Behavior_Service_job_meets_deadline@{u_1 u_2 u_3 Lean.u_1+1.0
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
   ImportedService.Prosa_Behavior_Job_JobDeadline Job
     inst_9)
  (j : Job) =>
ImportedService.Prosa_Validation_ServiceInterface_completedByProjection Job
  inst_9
  PState sched
  inst_16 j
  (ImportedService.Prosa_Behavior_Job_JobDeadline_job_deadline Job
     inst_9
     inst_19
     j)
     : forall (Job : ImportedService.Prosa_Behavior_Job_JobType)
         (inst_3 : ImportedService.DecidableEq Job)
         (PState : ImportedService.Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3),
       ImportedService.Prosa_Behavior_Schedule_schedule Job
         inst_3 PState ->
       ImportedService.Prosa_Behavior_Job_JobCost Job
         inst_3 ->
       ImportedService.Prosa_Behavior_Job_JobDeadline Job
         inst_3 ->
       Job -> ImportedService.Bool

Arguments ImportedService.Prosa_Behavior_Service_job_meets_deadline Job
  inst_3 PState sched
  inst_10
  inst_13 j
```
