# `service`

- Kind (Rocq): Definition
- Rocq: `prosa.behavior.service.service`
- Lean: `Prosa.Behavior.Service.service`
- Certificate: ``

## Official Rocq

```coq
service :
forall {Job : JobType} {PState : ProcessorState Job},
@schedule Job PState -> Equality.sort Job -> instant -> nat

service is not universe polymorphic
Arguments service {Job PState} sched j t
service is transparent
Expands to: Constant prosa.behavior.service.service
Declared in library prosa.behavior.service, line 31, characters 13-20
@service
     : forall (Job : JobType) (PState : ProcessorState Job),
       @schedule Job PState -> Equality.sort Job -> instant -> nat
```

Body:

```coq
service =
fun (Job : JobType) (PState : ProcessorState Job) (sched : @schedule Job PState) (j : Equality.sort Job) =>
     : forall {Job : JobType} {PState : ProcessorState Job},
       @schedule Job PState -> Equality.sort Job -> instant -> nat

Arguments service {Job PState} sched j t
```

## Lean

```lean
@Prosa.Behavior.Service.service : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
      Prosa.Behavior.Schedule.schedule PState → Job → Prosa.Behavior.Time.instant → Prosa.Behavior.Job.work
def Prosa.Behavior.Service.service.{u_1, u_2, u_3} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
      Prosa.Behavior.Schedule.schedule PState → Job → Prosa.Behavior.Time.instant → Prosa.Behavior.Job.work :=
fun {Job} [DecidableEq Job] {PState} sched j t => Prosa.Behavior.Service.service_during sched j 0 t
```

## Lean, imported into Rocq

```coq
ImportedService.Prosa_Behavior_Service_service
     : forall (Job : ImportedService.Prosa_Behavior_Job_JobType)
         (inst_3 : ImportedService.DecidableEq Job)
         (PState : ImportedService.Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3),
       ImportedService.Prosa_Behavior_Schedule_schedule Job
         inst_3 PState ->
       Job -> ImportedService.Prosa_Behavior_Time_instant -> ImportedService.Prosa_Behavior_Job_work
```

Body:

```coq
ImportedService.Prosa_Behavior_Service_service@{u_1 u_2 u_3 Lean.u_1+1.0 Lean.max__u_1+1_u_2+2_u_3+2.0
Lean.u_2+1.0 Lean.u_3+1.0 Lean.u_1+2.0 Lean.u_3+2.0} =
fun (Job : ImportedService.Prosa_Behavior_Job_JobType)
  (inst_9 : 
   ImportedService.DecidableEq Job)
  (PState : ImportedService.Prosa_Behavior_Schedule_ProcessorState Job
              inst_9)
  (sched : ImportedService.Prosa_Behavior_Schedule_schedule Job
             inst_9
             PState)
  (j : Job) (t : ImportedService.Prosa_Behavior_Time_instant) =>
ImportedService.Prosa_Validation_ServiceInterface_serviceDuringProjection Job
  inst_9
  PState sched j
  (ImportedService.OfNat_ofNat_inst1 ImportedService.Prosa_Behavior_Time_instant 0
     (ImportedService.instOfNatNat 0))
  t
     : forall (Job : ImportedService.Prosa_Behavior_Job_JobType)
         (inst_3 : ImportedService.DecidableEq Job)
         (PState : ImportedService.Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3),
       ImportedService.Prosa_Behavior_Schedule_schedule Job
         inst_3 PState ->
       Job -> ImportedService.Prosa_Behavior_Time_instant -> ImportedService.Prosa_Behavior_Job_work

Arguments ImportedService.Prosa_Behavior_Service_service Job
  inst_3 PState sched j t
```
