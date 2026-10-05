# `Scheduler`

- Kind (Rocq): Definition
- Rocq: `prosa.results.transfer_schedulability.paper_model.Scheduler`
- Lean: `Prosa.Results.TransferSchedulability.PaperModel.Scheduler`
- Certificate: `Scheduler_source_total, Scheduler_target_total, Scheduler_generic_source_total, Scheduler_generic_target_total`

## Official Rocq

```coq
Scheduler :
forall (Omega : Type) (Job : JobType),
ProcessorState Job ->
JobArrival Job ->
forall {Job0 : JobType}, JobPredecessors Job0 -> forall {Job1 : JobType}, SystemEvolutions Omega Job1 -> Type

Scheduler is not universe polymorphic
Arguments Scheduler Omega%type_scope Job {PState H Job0 H0 Job1 H1}
Scheduler is transparent
Expands to: Constant prosa.results.transfer_schedulability.paper_model.Scheduler
Declared in library prosa.results.transfer_schedulability.paper_model, line 143, characters 13-22
Scheduler
     : forall (Omega : Type) (Job : JobType),
       ProcessorState Job ->
       JobArrival Job ->
       forall Job0 : JobType,
       JobPredecessors Job0 -> forall Job1 : JobType, SystemEvolutions Omega Job1 -> Type
```

Body:

```coq
Scheduler =
fun (Omega : Type) (Job : JobType) (PState : ProcessorState Job) =>
fun=> (fun Job0 : JobType => fun=> (fun Job1 : JobType => fun=> Omega -> @schedule Job PState))
     : forall (Omega : Type) (Job : JobType),
       ProcessorState Job ->
       JobArrival Job ->
       forall {Job0 : JobType},
       JobPredecessors Job0 -> forall {Job1 : JobType}, SystemEvolutions Omega Job1 -> Type

Arguments Scheduler Omega%type_scope Job {PState H Job0 H0 Job1 H1}
```

## Lean

```lean
Prosa.Results.TransferSchedulability.PaperModel.Scheduler : (Omega : Type) →
  (Job : Prosa.Behavior.Job.JobType) →
    [inst : DecidableEq Job] →
      Prosa.Behavior.Schedule.ProcessorState Job →
        Prosa.Behavior.Job.JobArrival Job →
          (Job0 : Prosa.Behavior.Job.JobType) →
            [inst : DecidableEq Job0] →
              Prosa.Results.TransferSchedulability.PaperModel.JobPredecessors Job0 →
                (Job1 : Prosa.Behavior.Job.JobType) →
                  [inst : DecidableEq Job1] →
                    Prosa.Results.TransferSchedulability.PaperModel.SystemEvolutions Omega Job1 → Type u_2
```

Body:

```lean
def Prosa.Results.TransferSchedulability.PaperModel.Scheduler.{u_1, u_2, u_3, u_4, u_5} : (Omega : Type) →
  (Job : Prosa.Behavior.Job.JobType) →
    [inst : DecidableEq Job] →
      Prosa.Behavior.Schedule.ProcessorState Job →
        Prosa.Behavior.Job.JobArrival Job →
          (Job0 : Prosa.Behavior.Job.JobType) →
            [inst : DecidableEq Job0] →
              Prosa.Results.TransferSchedulability.PaperModel.JobPredecessors Job0 →
                (Job1 : Prosa.Behavior.Job.JobType) →
                  [inst : DecidableEq Job1] →
                    Prosa.Results.TransferSchedulability.PaperModel.SystemEvolutions Omega Job1 → Type u_2 :=
fun Omega Job [DecidableEq Job] PState x Job0 [DecidableEq Job0] x_1 Job1 [DecidableEq Job1] x_2 =>
  Omega → Prosa.Behavior.Schedule.schedule PState
```

## Lean, imported into Rocq

```coq
Prosa_Results_TransferSchedulability_PaperModel_Scheduler
     : forall (Omega : Type) (Job : Prosa_Behavior_Job_JobType)
         (inst_4 : 
          DecidableEq Job),
       Prosa_Behavior_Schedule_ProcessorState Job
         inst_4 ->
       Prosa_Behavior_Job_JobArrival Job
         inst_4 ->
       forall (Job0 : Prosa_Behavior_Job_JobType)
         (inst_13 : 
          DecidableEq Job0),
       Prosa_Results_TransferSchedulability_PaperModel_JobPredecessors Job0
         inst_13 ->
       forall (Job1 : Prosa_Behavior_Job_JobType)
         (inst_20 : 
          DecidableEq Job1),
       Prosa_Results_TransferSchedulability_PaperModel_SystemEvolutions Omega Job1
         inst_20 ->
       Type
```

Body:

```coq
Prosa_Results_TransferSchedulability_PaperModel_Scheduler@{u_1 u_2 u_3 u_4 u_5 Lean.u_1+1.0
Lean.max__u_1+1_u_2+2_u_3+2.0 Lean.u_2+1.0 Lean.u_3+1.0 Lean.u_4+1.0 Lean.u_5+1.0 Lean.u_1+2.0 Lean.u_3+2.0
Lean.u_4+2.0 Lean.u_5+2.0} =
fun (Omega : Type) (Job : Prosa_Behavior_Job_JobType)
  (inst_4 : DecidableEq Job)
  (PState : Prosa_Behavior_Schedule_ProcessorState Job
              inst_4)
  (_ : Prosa_Behavior_Job_JobArrival Job
         inst_4)
  (Job0 : Prosa_Behavior_Job_JobType)
  (inst_13 : DecidableEq Job0)
  (_ : Prosa_Results_TransferSchedulability_PaperModel_JobPredecessors Job0
         inst_13)
  (Job1 : Prosa_Behavior_Job_JobType)
  (inst_20 : DecidableEq Job1)
  (_ : Prosa_Results_TransferSchedulability_PaperModel_SystemEvolutions Omega Job1
         inst_20) =>
Omega ->
Prosa_Behavior_Schedule_schedule Job
  inst_4 PState
     : forall (Omega : Type) (Job : Prosa_Behavior_Job_JobType)
         (inst_4 : 
          DecidableEq Job),
       Prosa_Behavior_Schedule_ProcessorState Job
         inst_4 ->
       Prosa_Behavior_Job_JobArrival Job
         inst_4 ->
       forall (Job0 : Prosa_Behavior_Job_JobType)
         (inst_13 : 
          DecidableEq Job0),
       Prosa_Results_TransferSchedulability_PaperModel_JobPredecessors Job0
         inst_13 ->
       forall (Job1 : Prosa_Behavior_Job_JobType)
         (inst_20 : 
          DecidableEq Job1),
       Prosa_Results_TransferSchedulability_PaperModel_SystemEvolutions Omega Job1
         inst_20 ->
       Type

Arguments Prosa_Results_TransferSchedulability_PaperModel_Scheduler Omega%_type_scope 
  Job inst_4 
  PState x____at___Prosa_Results_TransferSchedulability_PaperModel1233244080__hygCtx__hyg9 
  Job0 inst_13
  x____at___Prosa_Results_TransferSchedulability_PaperModel1233244080__hygCtx__hyg16 
  Job1 inst_20
  x____at___Prosa_Results_TransferSchedulability_PaperModel1233244080__hygCtx__hyg23
```
