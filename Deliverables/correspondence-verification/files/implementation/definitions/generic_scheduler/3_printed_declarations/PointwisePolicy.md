# `PointwisePolicy`

- Kind (Rocq): Definition
- Rocq: `prosa.implementation.definitions.generic_scheduler.PointwisePolicy`
- Lean: `Prosa.Implementation.Definitions.GenericScheduler.PointwisePolicy`
- Certificate: `gs_pointwise_policy_application`

## Official Rocq

```coq
PointwisePolicy : forall {Job : JobType}, ProcessorState Job -> Type

PointwisePolicy is not universe polymorphic
Arguments PointwisePolicy {Job} PState
PointwisePolicy is transparent
Expands to: Constant prosa.implementation.definitions.generic_scheduler.PointwisePolicy
Declared in library prosa.implementation.definitions.generic_scheduler, line 19, characters 13-28
@PointwisePolicy
     : forall Job : JobType, ProcessorState Job -> Type
```

Body:

```coq
PointwisePolicy =
fun (Job : JobType) (PState : ProcessorState Job) => @schedule Job PState -> instant -> @State Job PState
     : forall {Job : JobType}, ProcessorState Job -> Type

Arguments PointwisePolicy {Job} PState
```

## Lean

```lean
@Prosa.Implementation.Definitions.GenericScheduler.PointwisePolicy : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] → Prosa.Behavior.Schedule.ProcessorState Job → Type u_1
def Prosa.Implementation.Definitions.GenericScheduler.PointwisePolicy.{u, v, w} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] → Prosa.Behavior.Schedule.ProcessorState Job → Type u :=
fun {Job} [DecidableEq Job] PState =>
  Prosa.Behavior.Schedule.schedule PState →
    Prosa.Behavior.Time.instant → Prosa.Behavior.Schedule.ProcessorState.State Job
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Definitions_GenericScheduler_PointwisePolicy
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : 
          DecidableEq Job),
       Prosa_Behavior_Schedule_ProcessorState Job
         inst_3 ->
       Type
```

Body:

```coq
Prosa_Implementation_Definitions_GenericScheduler_PointwisePolicy@{u v w Lean.u+1.0 Lean.v+1.0 Lean.w+1.0
Lean.max__u+2_v+2_w+1.0 Lean.v+2.0 Lean.w+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (PState : Prosa_Behavior_Schedule_ProcessorState Job
              inst_3) =>
Prosa_Behavior_Schedule_schedule Job
  inst_3 PState ->
Prosa_Behavior_Time_instant ->
Prosa_Behavior_Schedule_ProcessorState_State Job
  inst_3 PState
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : 
          DecidableEq Job),
       Prosa_Behavior_Schedule_ProcessorState Job
         inst_3 ->
       Type

Arguments Prosa_Implementation_Definitions_GenericScheduler_PointwisePolicy Job
  inst_3 
  PState
```
