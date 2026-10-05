# `generic_schedule`

- Kind (Rocq): Definition
- Rocq: `prosa.implementation.definitions.generic_scheduler.generic_schedule`
- Lean: `Prosa.Implementation.Definitions.GenericScheduler.generic_schedule`
- Certificate: `gs_generic_schedule_correspondence`

## Official Rocq

```coq
generic_schedule :
forall {Job : JobType} {PState : ProcessorState Job},
@PointwisePolicy Job PState -> @State Job PState -> instant -> @State Job PState

generic_schedule is not universe polymorphic
Arguments generic_schedule {Job PState} policy idle_state t
generic_schedule is transparent
Expands to: Constant prosa.implementation.definitions.generic_scheduler.generic_schedule
Declared in library prosa.implementation.definitions.generic_scheduler, line 50, characters 13-29
@generic_schedule
     : forall (Job : JobType) (PState : ProcessorState Job),
       @PointwisePolicy Job PState -> @State Job PState -> instant -> @State Job PState
```

Body:

```coq
generic_schedule =
fun (Job : JobType) (PState : ProcessorState Job) (policy : @PointwisePolicy Job PState)
  (idle_state : @State Job PState) (t : instant) =>
@schedule_up_to Job PState policy idle_state t t
     : forall {Job : JobType} {PState : ProcessorState Job},
       @PointwisePolicy Job PState -> @State Job PState -> instant -> @State Job PState

Arguments generic_schedule {Job PState} policy idle_state t
```

## Lean

```lean
@Prosa.Implementation.Definitions.GenericScheduler.generic_schedule : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
      Prosa.Implementation.Definitions.GenericScheduler.PointwisePolicy PState →
        Prosa.Behavior.Schedule.ProcessorState.State Job →
          Prosa.Behavior.Time.instant → Prosa.Behavior.Schedule.ProcessorState.State Job
def Prosa.Implementation.Definitions.GenericScheduler.generic_schedule.{u, v, w} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
      Prosa.Implementation.Definitions.GenericScheduler.PointwisePolicy PState →
        Prosa.Behavior.Schedule.ProcessorState.State Job →
          Prosa.Behavior.Time.instant → Prosa.Behavior.Schedule.ProcessorState.State Job :=
fun {Job} [DecidableEq Job] {PState} policy idle_state t =>
  Prosa.Implementation.Definitions.GenericScheduler.schedule_up_to policy idle_state t t
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Definitions_GenericScheduler_generic_schedule
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : 
          DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3),
       Prosa_Implementation_Definitions_GenericScheduler_PointwisePolicy Job
         inst_3 PState ->
       Prosa_Behavior_Schedule_ProcessorState_State Job
         inst_3 PState ->
       Prosa_Behavior_Time_instant ->
       Prosa_Behavior_Schedule_ProcessorState_State Job
         inst_3 PState
```

Body:

```coq
Prosa_Implementation_Definitions_GenericScheduler_generic_schedule@{u v w Lean.u+1.0 Lean.v+1.0 Lean.w+1.0
Lean.u+2.0 Lean.max__u+2_v+2_w+1.0 Lean.v+2.0 Lean.w+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (PState : Prosa_Behavior_Schedule_ProcessorState Job
              inst_3)
  (policy : Prosa_Implementation_Definitions_GenericScheduler_PointwisePolicy Job
              inst_3 PState)
  (idle_state : Prosa_Behavior_Schedule_ProcessorState_State Job
                  inst_3
                  PState)
  (t : Prosa_Behavior_Time_instant) =>
Prosa_Implementation_Definitions_GenericScheduler_schedule_up_to Job
  inst_3 PState policy
  idle_state t t
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : 
          DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3),
       Prosa_Implementation_Definitions_GenericScheduler_PointwisePolicy Job
         inst_3 PState ->
       Prosa_Behavior_Schedule_ProcessorState_State Job
         inst_3 PState ->
       Prosa_Behavior_Time_instant ->
       Prosa_Behavior_Schedule_ProcessorState_State Job
         inst_3 PState

Arguments Prosa_Implementation_Definitions_GenericScheduler_generic_schedule Job
  inst_3 
  PState policy idle_state t
```
