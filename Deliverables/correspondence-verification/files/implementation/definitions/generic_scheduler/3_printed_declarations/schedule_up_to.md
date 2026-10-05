# `schedule_up_to`

- Kind (Rocq): Fixpoint
- Rocq: `prosa.implementation.definitions.generic_scheduler.schedule_up_to`
- Lean: `Prosa.Implementation.Definitions.GenericScheduler.schedule_up_to`
- Certificate: `gs_prefix_correspondence`

## Official Rocq

```coq
schedule_up_to :
forall {Job : JobType} {PState : ProcessorState Job},
@PointwisePolicy Job PState -> @State Job PState -> instant -> @schedule Job PState

schedule_up_to is not universe polymorphic
Arguments schedule_up_to {Job PState} policy idle_state h _
schedule_up_to is transparent
Expands to: Constant prosa.implementation.definitions.generic_scheduler.schedule_up_to
Declared in library prosa.implementation.definitions.generic_scheduler, line 40, characters 2-176
@schedule_up_to
     : forall (Job : JobType) (PState : ProcessorState Job),
       @PointwisePolicy Job PState -> @State Job PState -> instant -> @schedule Job PState
```

Body:

```coq
schedule_up_to =
fun (Job : JobType) (PState : ProcessorState Job) (policy : @PointwisePolicy Job PState)
  (idle_state : @State Job PState) =>
fix schedule_up_to (h : instant) : @schedule Job PState :=
  let prefix := match h with
                | 0 => @empty_schedule Job PState idle_state
                | h'.+1 => schedule_up_to h'
                end in
  @replace_at Job PState prefix h (policy prefix h)
     : forall {Job : JobType} {PState : ProcessorState Job},
       @PointwisePolicy Job PState -> @State Job PState -> instant -> @schedule Job PState

Arguments schedule_up_to {Job PState} policy idle_state h _
```

## Lean

```lean
@Prosa.Implementation.Definitions.GenericScheduler.schedule_up_to : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
      Prosa.Implementation.Definitions.GenericScheduler.PointwisePolicy PState →
        Prosa.Behavior.Schedule.ProcessorState.State Job →
          Prosa.Behavior.Time.instant → Prosa.Behavior.Schedule.schedule PState
def Prosa.Implementation.Definitions.GenericScheduler.schedule_up_to.{u, v, w} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
      Prosa.Implementation.Definitions.GenericScheduler.PointwisePolicy PState →
        Prosa.Behavior.Schedule.ProcessorState.State Job →
          Prosa.Behavior.Time.instant → Prosa.Behavior.Schedule.schedule PState :=
fun {Job} [DecidableEq Job] {PState} policy idle_state x =>
  Nat.brecOn x (Prosa.Implementation.Definitions.GenericScheduler.schedule_up_to._f policy idle_state)
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Definitions_GenericScheduler_schedule_up_to
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
       Prosa_Behavior_Schedule_schedule Job
         inst_3 PState
```

Body:

```coq
Prosa_Implementation_Definitions_GenericScheduler_schedule_up_to@{u v w Lean.u+1.0 Lean.v+1.0 Lean.w+1.0
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
  (x____at___Prosa_Implementation_Definitions_GenericScheduler375435180__hygCtx__hyg15 : Prosa_Behavior_Time_instant) =>
Nat_brecOn
  (fun _ : Prosa_Behavior_Time_instant =>
   Prosa_Behavior_Schedule_schedule Job
     inst_3 PState)
  x____at___Prosa_Implementation_Definitions_GenericScheduler375435180__hygCtx__hyg15
  (Prosa_Implementation_Definitions_GenericScheduler_schedule_up_to__f Job
     inst_3 PState policy
     idle_state)
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
       Prosa_Behavior_Schedule_schedule Job
         inst_3 PState

Arguments Prosa_Implementation_Definitions_GenericScheduler_schedule_up_to Job
  inst_3 
  PState policy idle_state a____at____internal__hyg0 a____at____internal__hyg0
```
