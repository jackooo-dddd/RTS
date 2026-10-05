# `remaining_cost`

- Kind (Rocq): Definition
- Rocq: `prosa.behavior.service.remaining_cost`
- Lean: `Prosa.Behavior.Service.remaining_cost`
- Certificate: ``

## Official Rocq

```coq
remaining_cost :
forall {Job : JobType} {PState : ProcessorState Job},
@schedule Job PState -> JobCost Job -> Equality.sort Job -> instant -> nat

remaining_cost is not universe polymorphic
Arguments remaining_cost {Job PState} sched {H} j t
remaining_cost is transparent
Expands to: Constant prosa.behavior.service.remaining_cost
Declared in library prosa.behavior.service, line 71, characters 13-27
@remaining_cost
     : forall (Job : JobType) (PState : ProcessorState Job),
       @schedule Job PState -> JobCost Job -> Equality.sort Job -> instant -> nat
```

Body:

```coq
remaining_cost =
fun (Job : JobType) (PState : ProcessorState Job) (sched : @schedule Job PState) 
  (H : JobCost Job) (j : Equality.sort Job) (t : instant) =>
@job_cost Job H j - @service Job PState sched j t
     : forall {Job : JobType} {PState : ProcessorState Job},
       @schedule Job PState -> JobCost Job -> Equality.sort Job -> instant -> nat

Arguments remaining_cost {Job PState} sched {H} j t
```

## Lean

```lean
@Prosa.Behavior.Service.remaining_cost : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
      Prosa.Behavior.Schedule.schedule PState →
        [Prosa.Behavior.Job.JobCost Job] → Job → Prosa.Behavior.Time.instant → Prosa.Behavior.Job.work
def Prosa.Behavior.Service.remaining_cost.{u_1, u_2, u_3} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
      Prosa.Behavior.Schedule.schedule PState →
        [Prosa.Behavior.Job.JobCost Job] → Job → Prosa.Behavior.Time.instant → Prosa.Behavior.Job.work :=
fun {Job} [DecidableEq Job] {PState} sched [Prosa.Behavior.Job.JobCost Job] j t =>
  Prosa.Behavior.Job.job_cost j - Prosa.Behavior.Service.service sched j t
```

## Lean, imported into Rocq

```coq
ImportedService.Prosa_Behavior_Service_remaining_cost
     : forall (Job : ImportedService.Prosa_Behavior_Job_JobType)
         (inst_3 : ImportedService.DecidableEq Job)
         (PState : ImportedService.Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3),
       ImportedService.Prosa_Behavior_Schedule_schedule Job
         inst_3 PState ->
       ImportedService.Prosa_Behavior_Job_JobCost Job
         inst_3 ->
       Job -> ImportedService.Prosa_Behavior_Time_instant -> ImportedService.Prosa_Behavior_Job_work
```

Body:

```coq
ImportedService.Prosa_Behavior_Service_remaining_cost@{u_1 u_2 u_3 Lean.u_1+1.0 Lean.max__u_1+1_u_2+2_u_3+2.0
Lean.u_2+1.0 Lean.u_3+1.0 Lean.u_1+2.0 Lean.u_3+2.0} =
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
  (j : Job) (t : ImportedService.Prosa_Behavior_Time_instant) =>
ImportedService.HSub_hSub_inst7 ImportedService.Prosa_Behavior_Job_work
  ImportedService.Prosa_Behavior_Job_work ImportedService.Prosa_Behavior_Job_work
  (ImportedService.instHSub_inst1 ImportedService.Prosa_Behavior_Job_work ImportedService.instSubNat)
  (ImportedService.Prosa_Behavior_Job_JobCost_job_cost Job
     inst_9
     inst_16
     j)
  (ImportedService.Prosa_Validation_ServiceInterface_serviceProjection Job
     inst_9
     PState sched j t)
     : forall (Job : ImportedService.Prosa_Behavior_Job_JobType)
         (inst_3 : ImportedService.DecidableEq Job)
         (PState : ImportedService.Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3),
       ImportedService.Prosa_Behavior_Schedule_schedule Job
         inst_3 PState ->
       ImportedService.Prosa_Behavior_Job_JobCost Job
         inst_3 ->
       Job -> ImportedService.Prosa_Behavior_Time_instant -> ImportedService.Prosa_Behavior_Job_work

Arguments ImportedService.Prosa_Behavior_Service_remaining_cost Job
  inst_3 PState sched
  inst_10 j t
```
