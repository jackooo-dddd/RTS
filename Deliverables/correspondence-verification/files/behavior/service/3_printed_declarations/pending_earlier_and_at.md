# `pending_earlier_and_at`

- Kind (Rocq): Definition
- Rocq: `prosa.behavior.service.pending_earlier_and_at`
- Lean: `Prosa.Behavior.Service.pending_earlier_and_at`
- Certificate: ``

## Official Rocq

```coq
pending_earlier_and_at :
forall {Job : JobType} {PState : ProcessorState Job},
@schedule Job PState -> JobCost Job -> JobArrival Job -> Equality.sort Job -> instant -> bool

pending_earlier_and_at is not universe polymorphic
Arguments pending_earlier_and_at {Job PState} sched {H H1} j t
pending_earlier_and_at is transparent
Expands to: Constant prosa.behavior.service.pending_earlier_and_at
Declared in library prosa.behavior.service, line 66, characters 13-35
@pending_earlier_and_at
     : forall (Job : JobType) (PState : ProcessorState Job),
       @schedule Job PState -> JobCost Job -> JobArrival Job -> Equality.sort Job -> instant -> bool
```

Body:

```coq
pending_earlier_and_at =
fun (Job : JobType) (PState : ProcessorState Job) (sched : @schedule Job PState) 
  (H : JobCost Job) (H1 : JobArrival Job) (j : Equality.sort Job) (t : instant) =>
@arrived_before Job H1 j t && ~~ @completed_by Job PState sched H j t
     : forall {Job : JobType} {PState : ProcessorState Job},
       @schedule Job PState -> JobCost Job -> JobArrival Job -> Equality.sort Job -> instant -> bool

Arguments pending_earlier_and_at {Job PState} sched {H H1} j t
```

## Lean

```lean
@Prosa.Behavior.Service.pending_earlier_and_at : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
      Prosa.Behavior.Schedule.schedule PState →
        [Prosa.Behavior.Job.JobCost Job] →
          [Prosa.Behavior.Job.JobArrival Job] → Job → Prosa.Behavior.Time.instant → Bool
def Prosa.Behavior.Service.pending_earlier_and_at.{u_1, u_2, u_3} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
      Prosa.Behavior.Schedule.schedule PState →
        [Prosa.Behavior.Job.JobCost Job] →
          [Prosa.Behavior.Job.JobArrival Job] → Job → Prosa.Behavior.Time.instant → Bool :=
fun {Job} [DecidableEq Job] {PState} sched [Prosa.Behavior.Job.JobCost Job] [Prosa.Behavior.Job.JobArrival Job] j t =>
  Prosa.Behavior.Arrival_sequence.arrived_before j t && !Prosa.Behavior.Service.completed_by sched j t
```

## Lean, imported into Rocq

```coq
ImportedService.Prosa_Behavior_Service_pending_earlier_and_at
     : forall (Job : ImportedService.Prosa_Behavior_Job_JobType)
         (inst_3 : ImportedService.DecidableEq Job)
         (PState : ImportedService.Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3),
       ImportedService.Prosa_Behavior_Schedule_schedule Job
         inst_3 PState ->
       ImportedService.Prosa_Behavior_Job_JobCost Job
         inst_3 ->
       ImportedService.Prosa_Behavior_Job_JobArrival Job
         inst_3 ->
       Job -> ImportedService.Prosa_Behavior_Time_instant -> ImportedService.Bool
```

Body:

```coq
ImportedService.Prosa_Behavior_Service_pending_earlier_and_at@{u_1 u_2 u_3 Lean.u_1+1.0
Lean.max__u_1+1_u_2+2_u_3+2.0 Lean.u_2+1.0 Lean.u_3+1.0 Lean.u_1+2.0 Lean.u_3+2.0} =
fun (Job : ImportedService.Prosa_Behavior_Job_JobType)
  (inst_9 : 
   ImportedService.DecidableEq Job)
  (PState : ImportedService.Prosa_Behavior_Schedule_ProcessorState Job
              inst_9)
  (sched : ImportedService.Prosa_Behavior_Schedule_schedule Job
             inst_9
             PState)
  (inst_16 : 
   ImportedService.Prosa_Behavior_Job_JobCost Job
     inst_9)
  (inst_19 : 
   ImportedService.Prosa_Behavior_Job_JobArrival Job
     inst_9)
  (j : Job) (t : ImportedService.Prosa_Behavior_Time_instant) =>
ImportedService.Bool_and
  (ImportedService.Prosa_Behavior_Arrival_sequence_arrived_before Job
     inst_9
     inst_19
     j t)
  (ImportedService.Bool_not
     (ImportedService.Prosa_Validation_ServiceInterface_completedByProjection Job
        inst_9
        PState sched
        inst_16
        j t))
     : forall (Job : ImportedService.Prosa_Behavior_Job_JobType)
         (inst_3 : ImportedService.DecidableEq Job)
         (PState : ImportedService.Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3),
       ImportedService.Prosa_Behavior_Schedule_schedule Job
         inst_3 PState ->
       ImportedService.Prosa_Behavior_Job_JobCost Job
         inst_3 ->
       ImportedService.Prosa_Behavior_Job_JobArrival Job
         inst_3 ->
       Job -> ImportedService.Prosa_Behavior_Time_instant -> ImportedService.Bool

Arguments ImportedService.Prosa_Behavior_Service_pending_earlier_and_at Job
  inst_3 PState sched
  inst_10
  inst_16 j t
```
