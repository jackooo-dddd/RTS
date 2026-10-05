# `service_during`

- Kind (Rocq): Definition
- Rocq: `prosa.behavior.service.service_during`
- Lean: `Prosa.Behavior.Service.service_during`
- Certificate: ``

## Official Rocq

```coq
service_during :
forall {Job : JobType} {PState : ProcessorState Job},
@schedule Job PState -> Equality.sort Job -> instant -> instant -> nat

service_during is not universe polymorphic
Arguments service_during {Job PState} sched j t1 t2
service_during is transparent
Expands to: Constant prosa.behavior.service.service_during
Declared in library prosa.behavior.service, line 26, characters 13-27
@service_during
     : forall (Job : JobType) (PState : ProcessorState Job),
       @schedule Job PState -> Equality.sort Job -> instant -> instant -> nat
```

Body:

```coq
service_during =
fun (Job : JobType) (PState : ProcessorState Job) (sched : @schedule Job PState) 
  (j : Equality.sort Job) (t1 t2 : instant) =>
\sum_(t1 <= t < t2) @service_at Job PState sched j t
     : forall {Job : JobType} {PState : ProcessorState Job},
       @schedule Job PState -> Equality.sort Job -> instant -> instant -> nat

Arguments service_during {Job PState} sched j t1 t2
```

## Lean

```lean
@Prosa.Behavior.Service.service_during : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
      Prosa.Behavior.Schedule.schedule PState →
        Job → Prosa.Behavior.Time.instant → Prosa.Behavior.Time.instant → Prosa.Behavior.Job.work
def Prosa.Behavior.Service.service_during.{u_1, u_2, u_3} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
      Prosa.Behavior.Schedule.schedule PState →
        Job → Prosa.Behavior.Time.instant → Prosa.Behavior.Time.instant → Prosa.Behavior.Job.work :=
fun {Job} [DecidableEq Job] {PState} sched j t1 t2 =>
  ∑ t ∈ Finset.Ico t1 t2, Prosa.Behavior.Service.service_at sched j t
```

## Lean, imported into Rocq

```coq
ImportedService.Prosa_Behavior_Service_service_during
     : forall (Job : ImportedService.Prosa_Behavior_Job_JobType)
         (inst_3 : ImportedService.DecidableEq Job)
         (PState : ImportedService.Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3),
       ImportedService.Prosa_Behavior_Schedule_schedule Job
         inst_3 PState ->
       Job ->
       ImportedService.Prosa_Behavior_Time_instant ->
       ImportedService.Prosa_Behavior_Time_instant -> ImportedService.Prosa_Behavior_Job_work
```

Body:

```coq
ImportedService.Prosa_Behavior_Service_service_during@{u_1 u_2 u_3 Lean.u_1+1.0 Lean.max__u_1+1_u_2+2_u_3+2.0
Lean.u_2+1.0 Lean.u_3+1.0 Lean.u_1+2.0 Lean.u_3+2.0} =
fun (Job : ImportedService.Prosa_Behavior_Job_JobType)
  (inst_9 : 
   ImportedService.DecidableEq Job)
  (PState : ImportedService.Prosa_Behavior_Schedule_ProcessorState Job
              inst_9)
  (sched : ImportedService.Prosa_Behavior_Schedule_schedule Job
             inst_9
             PState)
  (j : Job) (t1 t2 : ImportedService.Prosa_Behavior_Time_instant) =>
ImportedService.List_foldr_inst3 Nat ImportedService.Prosa_Behavior_Job_work Nat_add
  (ImportedService.OfNat_ofNat_inst1 ImportedService.Prosa_Behavior_Job_work 0
     (ImportedService.instOfNatNat 0))
  (ImportedService.List_map_inst3 ImportedService.Prosa_Behavior_Time_instant Nat
     (fun t : ImportedService.Prosa_Behavior_Time_instant =>
      ImportedService.Prosa_Validation_ServiceInterface_serviceAtProjection Job
        inst_9
        PState sched j t)
     (ImportedService.List_range' t1
        (ImportedService.HSub_hSub_inst7 ImportedService.Prosa_Behavior_Time_instant
           ImportedService.Prosa_Behavior_Time_instant ImportedService.Prosa_Behavior_Time_instant
           (ImportedService.instHSub_inst1 ImportedService.Prosa_Behavior_Time_instant
              ImportedService.instSubNat)
           t2 t1)
        (ImportedService.OfNat_ofNat_inst1 Nat 1 (ImportedService.instOfNatNat 1))))
     : forall (Job : ImportedService.Prosa_Behavior_Job_JobType)
         (inst_3 : ImportedService.DecidableEq Job)
         (PState : ImportedService.Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3),
       ImportedService.Prosa_Behavior_Schedule_schedule Job
         inst_3 PState ->
       Job ->
       ImportedService.Prosa_Behavior_Time_instant ->
       ImportedService.Prosa_Behavior_Time_instant -> ImportedService.Prosa_Behavior_Job_work

Arguments ImportedService.Prosa_Behavior_Service_service_during Job
  inst_3 PState sched j t1 t
```
