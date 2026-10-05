# `JobReady`

- Kind (Rocq): Class
- Rocq: `prosa.behavior.ready.JobReady`
- Lean: `Prosa.Behavior.Ready.JobReady`
- Certificate: ``

## Official Rocq

```coq
JobReady : forall Job : JobType, ProcessorState Job -> JobCost Job -> JobArrival Job -> Type

JobReady is not universe polymorphic
Arguments JobReady Job PState {jc ja}
Expands to: Inductive prosa.behavior.ready.JobReady
Declared in library prosa.behavior.ready, line 11, characters 6-14
JobReady
     : forall Job : JobType, ProcessorState Job -> JobCost Job -> JobArrival Job -> Type
```

## Lean

```lean
Prosa.Behavior.Ready.JobReady : (Job : Prosa.Behavior.Job.JobType) →
  [inst : DecidableEq Job] →
    Prosa.Behavior.Schedule.ProcessorState Job →
      [Prosa.Behavior.Job.JobCost Job] → [Prosa.Behavior.Job.JobArrival Job] → Type (max u_1 u_2)
```

## Lean, imported into Rocq

```coq
ImportedReady.Prosa_Behavior_Ready_JobReady
     : forall (Job : ImportedReady.Prosa_Behavior_Job_JobType)
         (inst_3 : ImportedReady.DecidableEq Job),
       ImportedReady.Prosa_Behavior_Schedule_ProcessorState Job
         inst_3 ->
       ImportedReady.Prosa_Behavior_Job_JobCost Job inst_3 ->
       ImportedReady.Prosa_Behavior_Job_JobArrival Job
         inst_3 ->
       Type
```
