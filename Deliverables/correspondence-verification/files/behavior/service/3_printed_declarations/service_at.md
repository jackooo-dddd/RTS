# `service_at`

- Kind (Rocq): Definition
- Rocq: `prosa.behavior.service.service_at`
- Lean: `Prosa.Behavior.Service.service_at`
- Certificate: ``

## Official Rocq

```coq
service_at :
forall {Job : JobType} {PState : ProcessorState Job},
@schedule Job PState -> Equality.sort Job -> instant -> work

service_at is not universe polymorphic
Arguments service_at {Job PState} sched j t
service_at is transparent
Expands to: Constant prosa.behavior.service.service_at
Declared in library prosa.behavior.service, line 17, characters 13-23
@service_at
     : forall (Job : JobType) (PState : ProcessorState Job),
       @schedule Job PState -> Equality.sort Job -> instant -> work
```

Body:

```coq
service_at =
fun (Job : JobType) (PState : ProcessorState Job) (sched : @schedule Job PState) 
  (j : Equality.sort Job) (t : instant) =>
@service_in Job PState j (sched t)
     : forall {Job : JobType} {PState : ProcessorState Job},
       @schedule Job PState -> Equality.sort Job -> instant -> work

Arguments service_at {Job PState} sched j t
```

## Lean

```lean
@Prosa.Behavior.Service.service_at : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
      Prosa.Behavior.Schedule.schedule PState → Job → Prosa.Behavior.Time.instant → Prosa.Behavior.Job.work
def Prosa.Behavior.Service.service_at.{u_1, u_2, u_3} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
      Prosa.Behavior.Schedule.schedule PState → Job → Prosa.Behavior.Time.instant → Prosa.Behavior.Job.work :=
fun {Job} [DecidableEq Job] {PState} sched j t => PState.service_in j (sched t)
```

## Lean, imported into Rocq

```coq
ImportedService.Prosa_Behavior_Service_service_at
     : forall (Job : ImportedService.Prosa_Behavior_Job_JobType)
         (inst_3 : ImportedService.DecidableEq Job)
         (PState : ImportedService.Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3),
       ImportedService.Prosa_Behavior_Schedule_schedule Job
         inst_3 PState ->
       Job -> ImportedService.Prosa_Behavior_Time_instant -> ImportedService.Prosa_Behavior_Job_work
```

Body:

```coq
ImportedService.Prosa_Behavior_Service_service_at@{u_1 u_2 u_3 Lean.u_1+1.0 Lean.max__u_1+1_u_2+2_u_3+2.0
Lean.u_2+1.0 Lean.u_3+1.0 Lean.u_1+2.0 Lean.u_3+2.0} =
fun (Job : ImportedService.Prosa_Behavior_Job_JobType)
  (inst_9 : 
   ImportedService.DecidableEq Job)
  (PState : ImportedService.Prosa_Behavior_Schedule_ProcessorState Job
              inst_9)
  (sched : ImportedService.Prosa_Behavior_Schedule_schedule Job
             inst_9
             PState)
  (j : Job) (t : ImportedService.Prosa_Behavior_Time_instant) =>
ImportedService.Prosa_Behavior_Schedule_ProcessorState_service_in Job
  inst_9
  PState j (sched t)
     : forall (Job : ImportedService.Prosa_Behavior_Job_JobType)
         (inst_3 : ImportedService.DecidableEq Job)
         (PState : ImportedService.Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3),
       ImportedService.Prosa_Behavior_Schedule_schedule Job
         inst_3 PState ->
       Job -> ImportedService.Prosa_Behavior_Time_instant -> ImportedService.Prosa_Behavior_Job_work

Arguments ImportedService.Prosa_Behavior_Service_service_at Job
  inst_3 PState sched j t
```
