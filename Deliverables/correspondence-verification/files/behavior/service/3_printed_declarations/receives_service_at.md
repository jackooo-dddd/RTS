# `receives_service_at`

- Kind (Rocq): Definition
- Rocq: `prosa.behavior.service.receives_service_at`
- Lean: `Prosa.Behavior.Service.receives_service_at`
- Certificate: ``

## Official Rocq

```coq
receives_service_at :
forall {Job : JobType} {PState : ProcessorState Job},
@schedule Job PState -> Equality.sort Job -> instant -> bool

receives_service_at is not universe polymorphic
Arguments receives_service_at {Job PState} sched j t
receives_service_at is transparent
Expands to: Constant prosa.behavior.service.receives_service_at
Declared in library prosa.behavior.service, line 21, characters 13-32
@receives_service_at
     : forall (Job : JobType) (PState : ProcessorState Job),
       @schedule Job PState -> Equality.sort Job -> instant -> bool
```

Body:

```coq
receives_service_at =
fun (Job : JobType) (PState : ProcessorState Job) (sched : @schedule Job PState) 
  (j : Equality.sort Job) (t : instant) =>
0 < @service_at Job PState sched j t
     : forall {Job : JobType} {PState : ProcessorState Job},
       @schedule Job PState -> Equality.sort Job -> instant -> bool

Arguments receives_service_at {Job PState} sched j t
```

## Lean

```lean
@Prosa.Behavior.Service.receives_service_at : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
      Prosa.Behavior.Schedule.schedule PState → Job → Prosa.Behavior.Time.instant → Bool
def Prosa.Behavior.Service.receives_service_at.{u_1, u_2, u_3} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
      Prosa.Behavior.Schedule.schedule PState → Job → Prosa.Behavior.Time.instant → Bool :=
fun {Job} [DecidableEq Job] {PState} sched j t => decide (0 < Prosa.Behavior.Service.service_at sched j t)
```

## Lean, imported into Rocq

```coq
ImportedService.Prosa_Behavior_Service_receives_service_at
     : forall (Job : ImportedService.Prosa_Behavior_Job_JobType)
         (inst_3 : ImportedService.DecidableEq Job)
         (PState : ImportedService.Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3),
       ImportedService.Prosa_Behavior_Schedule_schedule Job
         inst_3 PState ->
       Job -> ImportedService.Prosa_Behavior_Time_instant -> ImportedService.Bool
```

Body:

```coq
ImportedService.Prosa_Behavior_Service_receives_service_at@{u_1 u_2 u_3 Lean.u_1+1.0
Lean.max__u_1+1_u_2+2_u_3+2.0 Lean.u_2+1.0 Lean.u_3+1.0 Lean.u_1+2.0 Lean.u_3+2.0} =
fun (Job : ImportedService.Prosa_Behavior_Job_JobType)
  (inst_9 : 
   ImportedService.DecidableEq Job)
  (PState : ImportedService.Prosa_Behavior_Schedule_ProcessorState Job
              inst_9)
  (sched : ImportedService.Prosa_Behavior_Schedule_schedule Job
             inst_9
             PState)
  (j : Job) (t : ImportedService.Prosa_Behavior_Time_instant) =>
ImportedService.Decidable_decide
  (ImportedService.LT_lt_inst1 ImportedService.Prosa_Behavior_Job_work ImportedService.instLTNat
     (ImportedService.OfNat_ofNat_inst1 ImportedService.Prosa_Behavior_Job_work 0
        (ImportedService.instOfNatNat 0))
     (ImportedService.Prosa_Validation_ServiceInterface_serviceAtProjection Job
        inst_9
        PState sched j t))
  (ImportedService.Nat_decLt
     (ImportedService.OfNat_ofNat_inst1 ImportedService.Prosa_Behavior_Job_work 0
        (ImportedService.instOfNatNat 0))
     (ImportedService.Prosa_Validation_ServiceInterface_serviceAtProjection Job
        inst_9
        PState sched j t))
     : forall (Job : ImportedService.Prosa_Behavior_Job_JobType)
         (inst_3 : ImportedService.DecidableEq Job)
         (PState : ImportedService.Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3),
       ImportedService.Prosa_Behavior_Schedule_schedule Job
         inst_3 PState ->
       Job -> ImportedService.Prosa_Behavior_Time_instant -> ImportedService.Bool

Arguments ImportedService.Prosa_Behavior_Service_receives_service_at Job
  inst_3 PState sched j t
```
