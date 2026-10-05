# `scheduled_at`

- Kind (Rocq): Definition
- Rocq: `prosa.behavior.service.scheduled_at`
- Lean: `Prosa.Behavior.Service.scheduled_at`
- Certificate: ``

## Official Rocq

```coq
scheduled_at :
forall {Job : JobType} {PState : ProcessorState Job},
@schedule Job PState -> Equality.sort Job -> instant -> bool

scheduled_at is not universe polymorphic
Arguments scheduled_at {Job PState} sched j t
scheduled_at is transparent
Expands to: Constant prosa.behavior.service.scheduled_at
Declared in library prosa.behavior.service, line 14, characters 13-25
@scheduled_at
     : forall (Job : JobType) (PState : ProcessorState Job),
       @schedule Job PState -> Equality.sort Job -> instant -> bool
```

Body:

```coq
scheduled_at =
fun (Job : JobType) (PState : ProcessorState Job) (sched : @schedule Job PState) 
  (j : Equality.sort Job) (t : instant) =>
@scheduled_in Job PState j (sched t)
     : forall {Job : JobType} {PState : ProcessorState Job},
       @schedule Job PState -> Equality.sort Job -> instant -> bool

Arguments scheduled_at {Job PState} sched j t
```

## Lean

```lean
@Prosa.Behavior.Service.scheduled_at : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
      Prosa.Behavior.Schedule.schedule PState → Job → Prosa.Behavior.Time.instant → Bool
def Prosa.Behavior.Service.scheduled_at.{u_1, u_2, u_3} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
      Prosa.Behavior.Schedule.schedule PState → Job → Prosa.Behavior.Time.instant → Bool :=
fun {Job} [DecidableEq Job] {PState} sched j t => PState.scheduled_in j (sched t)
```

## Lean, imported into Rocq

```coq
ImportedService.Prosa_Behavior_Service_scheduled_at
     : forall (Job : ImportedService.Prosa_Behavior_Job_JobType)
         (inst_3 : ImportedService.DecidableEq Job)
         (PState : ImportedService.Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3),
       ImportedService.Prosa_Behavior_Schedule_schedule Job
         inst_3 PState ->
       Job -> ImportedService.Prosa_Behavior_Time_instant -> ImportedService.Bool
```

Body:

```coq
ImportedService.Prosa_Behavior_Service_scheduled_at@{u_1 u_2 u_3 Lean.u_1+1.0 Lean.max__u_1+1_u_2+2_u_3+2.0
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
ImportedService.Prosa_Behavior_Schedule_ProcessorState_scheduled_in Job
  inst_9
  PState j (sched t)
     : forall (Job : ImportedService.Prosa_Behavior_Job_JobType)
         (inst_3 : ImportedService.DecidableEq Job)
         (PState : ImportedService.Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3),
       ImportedService.Prosa_Behavior_Schedule_schedule Job
         inst_3 PState ->
       Job -> ImportedService.Prosa_Behavior_Time_instant -> ImportedService.Bool

Arguments ImportedService.Prosa_Behavior_Service_scheduled_at Job
  inst_3 PState sched j t
```
