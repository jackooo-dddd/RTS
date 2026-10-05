# `completes_at`

- Kind (Rocq): Definition
- Rocq: `prosa.behavior.service.completes_at`
- Lean: `Prosa.Behavior.Service.completes_at`
- Certificate: ``

## Official Rocq

```coq
completes_at :
forall {Job : JobType} {PState : ProcessorState Job},
@schedule Job PState -> JobCost Job -> Equality.sort Job -> instant -> bool

completes_at is not universe polymorphic
Arguments completes_at {Job PState} sched {H} j t
completes_at is transparent
Expands to: Constant prosa.behavior.service.completes_at
Declared in library prosa.behavior.service, line 47, characters 13-25
@completes_at
     : forall (Job : JobType) (PState : ProcessorState Job),
       @schedule Job PState -> JobCost Job -> Equality.sort Job -> instant -> bool
```

Body:

```coq
completes_at =
fun (Job : JobType) (PState : ProcessorState Job) (sched : @schedule Job PState) 
  (H : JobCost Job) (j : Equality.sort Job) (t : instant) =>
(~~ @completed_by Job PState sched H j t.-1 || (t == 0)) && @completed_by Job PState sched H j t
     : forall {Job : JobType} {PState : ProcessorState Job},
       @schedule Job PState -> JobCost Job -> Equality.sort Job -> instant -> bool

Arguments completes_at {Job PState} sched {H} j t
```

## Lean

```lean
@Prosa.Behavior.Service.completes_at : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
      Prosa.Behavior.Schedule.schedule PState →
        [Prosa.Behavior.Job.JobCost Job] → Job → Prosa.Behavior.Time.instant → Bool
def Prosa.Behavior.Service.completes_at.{u_1, u_2, u_3} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
      Prosa.Behavior.Schedule.schedule PState →
        [Prosa.Behavior.Job.JobCost Job] → Job → Prosa.Behavior.Time.instant → Bool :=
fun {Job} [DecidableEq Job] {PState} sched [Prosa.Behavior.Job.JobCost Job] j t =>
  (!Prosa.Behavior.Service.completed_by sched j (t - 1) || decide (t = 0)) &&
    Prosa.Behavior.Service.completed_by sched j t
```

## Lean, imported into Rocq

```coq
ImportedService.Prosa_Behavior_Service_completes_at
     : forall (Job : ImportedService.Prosa_Behavior_Job_JobType)
         (inst_3 : ImportedService.DecidableEq Job)
         (PState : ImportedService.Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3),
       ImportedService.Prosa_Behavior_Schedule_schedule Job
         inst_3 PState ->
       ImportedService.Prosa_Behavior_Job_JobCost Job
         inst_3 ->
       Job -> ImportedService.Prosa_Behavior_Time_instant -> ImportedService.Bool
```

Body:

```coq
ImportedService.Prosa_Behavior_Service_completes_at@{u_1 u_2 u_3 Lean.u_1+1.0 Lean.max__u_1+1_u_2+2_u_3+2.0
Lean.u_2+1.0 Lean.u_3+1.0 Lean.u_1+2.0 Lean.u_3+2.0} =
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
  (j : Job) (t : ImportedService.Prosa_Behavior_Time_instant) =>
ImportedService.Bool_and
  (ImportedService.Bool_or
     (ImportedService.Bool_not
        (ImportedService.Prosa_Validation_ServiceInterface_completedByProjection Job
           inst_9
           PState sched
           inst_16
           j
           (ImportedService.HSub_hSub_inst7 ImportedService.Prosa_Behavior_Time_instant
              ImportedService.Prosa_Behavior_Time_instant ImportedService.Prosa_Behavior_Time_instant
              (ImportedService.instHSub_inst1 ImportedService.Prosa_Behavior_Time_instant
                 ImportedService.instSubNat)
              t
              (ImportedService.OfNat_ofNat_inst1 ImportedService.Prosa_Behavior_Time_instant 1
                 (ImportedService.instOfNatNat 1)))))
     (ImportedService.Decidable_decide
        (@eq ImportedService.Prosa_Behavior_Time_instant t
           (ImportedService.OfNat_ofNat_inst1 ImportedService.Prosa_Behavior_Time_instant 0
              (ImportedService.instOfNatNat 0)))
        (ImportedService.instDecidableEqNat t
           (ImportedService.OfNat_ofNat_inst1 ImportedService.Prosa_Behavior_Time_instant 0
              (ImportedService.instOfNatNat 0)))))
  (ImportedService.Prosa_Validation_ServiceInterface_completedByProjection Job
     inst_9
     PState sched
     inst_16 j
     t)
     : forall (Job : ImportedService.Prosa_Behavior_Job_JobType)
         (inst_3 : ImportedService.DecidableEq Job)
         (PState : ImportedService.Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3),
       ImportedService.Prosa_Behavior_Schedule_schedule Job
         inst_3 PState ->
       ImportedService.Prosa_Behavior_Job_JobCost Job
         inst_3 ->
       Job -> ImportedService.Prosa_Behavior_Time_instant -> ImportedService.Bool

Arguments ImportedService.Prosa_Behavior_Service_completes_at Job
  inst_3 PState sched
  inst_10 j t
```
