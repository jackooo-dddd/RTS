# `ProcessorState`

- Kind (Rocq): Class
- Rocq: `prosa.behavior.schedule.ProcessorState`
- Lean: `Prosa.Behavior.Schedule.ProcessorState`
- Certificate: ``

## Official Rocq

```coq
ProcessorState : JobType -> Type

ProcessorState is not universe polymorphic
Arguments ProcessorState Job
Expands to: Inductive prosa.behavior.schedule.ProcessorState
Declared in library prosa.behavior.schedule, line 22, characters 6-20
ProcessorState
     : JobType -> Type
```

## Lean

```lean
Prosa.Behavior.Schedule.ProcessorState : (Job : Prosa.Behavior.Job.JobType) →
  [DecidableEq Job] → Type (max (max u_3 (u_1 + 1)) (u_2 + 1))
```

## Lean, imported into Rocq

```coq
ImportedSchedule.Prosa_Behavior_Schedule_ProcessorState
     : forall Job : ImportedSchedule.Prosa_Behavior_Job_JobType, ImportedSchedule.DecidableEq Job -> Type
```
