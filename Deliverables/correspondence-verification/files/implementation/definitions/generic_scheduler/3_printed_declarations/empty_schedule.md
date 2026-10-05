# `empty_schedule`

- Kind (Rocq): Definition
- Rocq: `prosa.implementation.definitions.generic_scheduler.empty_schedule`
- Lean: `Prosa.Implementation.Definitions.GenericScheduler.empty_schedule`
- Certificate: `gs_empty_schedule_correspondence`

## Official Rocq

```coq
empty_schedule :
forall {Job : JobType} {PState : ProcessorState Job}, @State Job PState -> @schedule Job PState

empty_schedule is not universe polymorphic
Arguments empty_schedule {Job PState} idle_state _
empty_schedule is transparent
Expands to: Constant prosa.implementation.definitions.generic_scheduler.empty_schedule
Declared in library prosa.implementation.definitions.generic_scheduler, line 36, characters 13-27
@empty_schedule
     : forall (Job : JobType) (PState : ProcessorState Job), @State Job PState -> @schedule Job PState
```

Body:

```coq
empty_schedule =
fun (Job : JobType) (PState : ProcessorState Job) (idle_state : @State Job PState) => fun=> idle_state
     : forall {Job : JobType} {PState : ProcessorState Job}, @State Job PState -> @schedule Job PState

Arguments empty_schedule {Job PState} idle_state _
```

## Lean

```lean
@Prosa.Implementation.Definitions.GenericScheduler.empty_schedule : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
      Prosa.Behavior.Schedule.ProcessorState.State Job → Prosa.Behavior.Schedule.schedule PState
def Prosa.Implementation.Definitions.GenericScheduler.empty_schedule.{u, v, w} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
      Prosa.Behavior.Schedule.ProcessorState.State Job → Prosa.Behavior.Schedule.schedule PState :=
fun {Job} [DecidableEq Job] {PState} idle_state x => idle_state
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Definitions_GenericScheduler_empty_schedule
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : 
          DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3),
       Prosa_Behavior_Schedule_ProcessorState_State Job
         inst_3 PState ->
       Prosa_Behavior_Schedule_schedule Job
         inst_3 PState
```

Body:

```coq
Prosa_Implementation_Definitions_GenericScheduler_empty_schedule@{u v w Lean.u+1.0 Lean.v+1.0 Lean.w+1.0
Lean.max__u+2_v+2_w+1.0 Lean.v+2.0 Lean.w+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (PState : Prosa_Behavior_Schedule_ProcessorState Job
              inst_3)
  (idle_state : Prosa_Behavior_Schedule_ProcessorState_State Job
                  inst_3
                  PState)
  (_ : Prosa_Behavior_Time_instant) =>
idle_state
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : 
          DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3),
       Prosa_Behavior_Schedule_ProcessorState_State Job
         inst_3 PState ->
       Prosa_Behavior_Schedule_schedule Job
         inst_3 PState

Arguments Prosa_Implementation_Definitions_GenericScheduler_empty_schedule Job
  inst_3 
  PState idle_state a____at____internal__hyg0
```
