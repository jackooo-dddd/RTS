# `schedule`

- Kind (Rocq): Definition
- Rocq: `prosa.behavior.schedule.schedule`
- Lean: `Prosa.Behavior.Schedule.schedule`
- Certificate: ``

## Official Rocq

```coq
schedule : forall {Job : JobType}, ProcessorState Job -> Type

schedule is not universe polymorphic
Arguments schedule {Job} PState
schedule is transparent
Expands to: Constant prosa.behavior.schedule.schedule
Declared in library prosa.behavior.schedule, line 100, characters 11-19
@schedule
     : forall Job : JobType, ProcessorState Job -> Type
```

Body:

```coq
schedule =
fun (Job : JobType) (PState : ProcessorState Job) => instant -> @State Job PState
     : forall {Job : JobType}, ProcessorState Job -> Type

Arguments schedule {Job} PState
```

## Lean

```lean
@Prosa.Behavior.Schedule.schedule : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] → Prosa.Behavior.Schedule.ProcessorState Job → Type u_2
def Prosa.Behavior.Schedule.schedule.{u_1, u_2, u_3} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] → Prosa.Behavior.Schedule.ProcessorState Job → Type u_2 :=
fun {Job} [DecidableEq Job] PState => Prosa.Behavior.Time.instant → Prosa.Behavior.Schedule.ProcessorState.State Job
```

## Lean, imported into Rocq

```coq
ImportedSchedule.Prosa_Behavior_Schedule_schedule
     : forall (Job : ImportedSchedule.Prosa_Behavior_Job_JobType)
         (inst_3 : ImportedSchedule.DecidableEq Job),
       ImportedSchedule.Prosa_Behavior_Schedule_ProcessorState Job
         inst_3 ->
       Type
```

Body:

```coq
ImportedSchedule.Prosa_Behavior_Schedule_schedule@{u_1 u_2 u_3 Lean.u_1+1.0 Lean.max__u_1+1_u_2+2_u_3+2.0
Lean.u_2+1.0 Lean.u_3+1.0 Lean.u_1+2.0 Lean.u_3+2.0} =
fun (Job : ImportedSchedule.Prosa_Behavior_Job_JobType)
  (inst_3 : ImportedSchedule.DecidableEq Job)
  (PState : ImportedSchedule.Prosa_Behavior_Schedule_ProcessorState Job
              inst_3) =>
ImportedSchedule.Prosa_Behavior_Time_instant ->
ImportedSchedule.Prosa_Behavior_Schedule_ProcessorState_State Job
  inst_3 PState
     : forall (Job : ImportedSchedule.Prosa_Behavior_Job_JobType)
         (inst_3 : ImportedSchedule.DecidableEq Job),
       ImportedSchedule.Prosa_Behavior_Schedule_ProcessorState Job
         inst_3 ->
       Type

Arguments ImportedSchedule.Prosa_Behavior_Schedule_schedule Job
  inst_3 PState
```
