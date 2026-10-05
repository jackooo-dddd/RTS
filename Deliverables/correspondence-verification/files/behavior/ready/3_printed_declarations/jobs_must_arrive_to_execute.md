# `jobs_must_arrive_to_execute`

- Kind (Rocq): Definition
- Rocq: `prosa.behavior.ready.jobs_must_arrive_to_execute`
- Lean: `Prosa.Behavior.Ready.jobs_must_arrive_to_execute`
- Certificate: ``

## Official Rocq

```coq
jobs_must_arrive_to_execute :
forall {Job : JobType}, JobArrival Job -> forall {PState : ProcessorState Job}, @schedule Job PState -> Prop

jobs_must_arrive_to_execute is not universe polymorphic
Arguments jobs_must_arrive_to_execute {Job H PState} sched
jobs_must_arrive_to_execute is transparent
Expands to: Constant prosa.behavior.ready.jobs_must_arrive_to_execute
Declared in library prosa.behavior.ready, line 55, characters 13-40
@jobs_must_arrive_to_execute
     : forall Job : JobType,
       JobArrival Job -> forall PState : ProcessorState Job, @schedule Job PState -> Prop
```

Body:

```coq
jobs_must_arrive_to_execute =
fun (Job : JobType) (H : JobArrival Job) (PState : ProcessorState Job) (sched : @schedule Job PState) =>
forall (j : Equality.sort Job) (t : instant),
is_true (@scheduled_at Job PState sched j t) -> is_true (@has_arrived Job H j t)
     : forall {Job : JobType},
       JobArrival Job -> forall {PState : ProcessorState Job}, @schedule Job PState -> Prop

Arguments jobs_must_arrive_to_execute {Job H PState} sched
```

## Lean

```lean
@Prosa.Behavior.Ready.jobs_must_arrive_to_execute : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [Prosa.Behavior.Job.JobArrival Job] →
      {PState : Prosa.Behavior.Schedule.ProcessorState Job} → Prosa.Behavior.Schedule.schedule PState → Prop
def Prosa.Behavior.Ready.jobs_must_arrive_to_execute.{u_1, u_2, u_3} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [Prosa.Behavior.Job.JobArrival Job] →
      {PState : Prosa.Behavior.Schedule.ProcessorState Job} → Prosa.Behavior.Schedule.schedule PState → Prop :=
fun {Job} [DecidableEq Job] [Prosa.Behavior.Job.JobArrival Job] {PState} sched =>
  ∀ (j : Job) (t : Prosa.Behavior.Time.instant),
    Prosa.Behavior.Service.scheduled_at sched j t = true → Prosa.Behavior.Arrival_sequence.has_arrived j t = true
```

## Lean, imported into Rocq

```coq
ImportedReady.Prosa_Behavior_Ready_jobs_must_arrive_to_execute
     : forall (Job : ImportedReady.Prosa_Behavior_Job_JobType)
         (inst_3 : ImportedReady.DecidableEq Job),
       ImportedReady.Prosa_Behavior_Job_JobArrival Job
         inst_3 ->
       forall
         PState : ImportedReady.Prosa_Behavior_Schedule_ProcessorState Job
                    inst_3,
       ImportedReady.Prosa_Behavior_Schedule_schedule Job
         inst_3 PState ->
       SProp
```

Body:

```coq
ImportedReady.Prosa_Behavior_Ready_jobs_must_arrive_to_execute@{u_1 u_2 u_3 Lean.u_1+1.0
Lean.max__u_1+1_u_2+2_u_3+2.0 Lean.u_2+1.0 Lean.u_3+1.0 Lean.u_1+2.0 Lean.u_3+2.0} =
fun (Job : ImportedReady.Prosa_Behavior_Job_JobType)
  (inst_3 : 
   ImportedReady.DecidableEq Job)
  (inst_6 : 
   ImportedReady.Prosa_Behavior_Job_JobArrival Job
     inst_3)
  (PState : ImportedReady.Prosa_Behavior_Schedule_ProcessorState Job
              inst_3)
  (sched : ImportedReady.Prosa_Behavior_Schedule_schedule Job
             inst_3
             PState) =>
forall (j : Job) (t : ImportedReady.Prosa_Behavior_Time_instant),
@eq ImportedReady.Bool
  (ImportedReady.Prosa_Behavior_Service_scheduled_at Job
     inst_3
     PState sched j t)
  ImportedReady.Bool_true ->
@eq ImportedReady.Bool
  (ImportedReady.Prosa_Behavior_Arrival_sequence_has_arrived Job
     inst_3
     inst_6 j t)
  ImportedReady.Bool_true
     : forall (Job : ImportedReady.Prosa_Behavior_Job_JobType)
         (inst_3 : ImportedReady.DecidableEq Job),
       ImportedReady.Prosa_Behavior_Job_JobArrival Job
         inst_3 ->
       forall
         PState : ImportedReady.Prosa_Behavior_Schedule_ProcessorState Job
                    inst_3,
       ImportedReady.Prosa_Behavior_Schedule_schedule Job
         inst_3 PState ->
       SProp

Arguments ImportedReady.Prosa_Behavior_Ready_jobs_must_arrive_to_execute Job
  inst_3
  inst_6 PState sched
```
