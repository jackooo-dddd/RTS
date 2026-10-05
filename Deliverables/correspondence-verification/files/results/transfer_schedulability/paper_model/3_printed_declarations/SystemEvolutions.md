# `SystemEvolutions`

- Kind (Rocq): Class
- Rocq: `prosa.results.transfer_schedulability.paper_model.SystemEvolutions`
- Lean: `Prosa.Results.TransferSchedulability.PaperModel.SystemEvolutions`
- Certificate: `SystemEvolutions_source_total, SystemEvolutions_target_total`

## Official Rocq

```coq
SystemEvolutions : Type -> JobType -> Type

SystemEvolutions is template universe polymorphic
Arguments SystemEvolutions Omega%type_scope Job
Expands to: Inductive prosa.results.transfer_schedulability.paper_model.SystemEvolutions
Declared in library prosa.results.transfer_schedulability.paper_model, line 108, characters 6-22
SystemEvolutions
     : Type -> JobType -> Type
```

Body:

```coq
Record SystemEvolutions (Omega : Type) (Job : JobType) : Type := Build_SystemEvolutions
  { evo_costs : Omega -> JobCost Job;  evo_delays : Omega -> JobDelay Job }.

Arguments SystemEvolutions Omega%type_scope Job
Arguments Build_SystemEvolutions Omega%type_scope Job (evo_costs evo_delays)%function_scope
Arguments evo_costs {Omega}%type_scope {Job SystemEvolutions} _ _
Arguments evo_delays {Omega}%type_scope {Job SystemEvolutions} _
```

## Lean

```lean
Prosa.Results.TransferSchedulability.PaperModel.SystemEvolutions : Type →
  (Job : Prosa.Behavior.Job.JobType) → [DecidableEq Job] → Type u_1
```

Body:

```lean
class Prosa.Results.TransferSchedulability.PaperModel.SystemEvolutions.{u_1} (Omega : Type)
  (Job : Prosa.Behavior.Job.JobType) [DecidableEq Job] : Type u_1
number of parameters: 3
fields:
  Prosa.Results.TransferSchedulability.PaperModel.SystemEvolutions.evo_costs : Omega → Prosa.Behavior.Job.JobCost Job
  Prosa.Results.TransferSchedulability.PaperModel.SystemEvolutions.evo_delays : Omega →
      Prosa.Results.TransferSchedulability.PaperModel.JobDelay Job
constructor:
  Prosa.Results.TransferSchedulability.PaperModel.SystemEvolutions.mk.{u_1} {Omega : Type}
    {Job : Prosa.Behavior.Job.JobType} [DecidableEq Job] (evo_costs : Omega → Prosa.Behavior.Job.JobCost Job)
    (evo_delays : Omega → Prosa.Results.TransferSchedulability.PaperModel.JobDelay Job) :
    Prosa.Results.TransferSchedulability.PaperModel.SystemEvolutions Omega Job
```

## Lean, imported into Rocq

```coq
Prosa_Results_TransferSchedulability_PaperModel_SystemEvolutions
     : Type -> forall Job : Prosa_Behavior_Job_JobType, DecidableEq Job -> Type
```

Body:

```coq
Record
Prosa_Results_TransferSchedulability_PaperModel_SystemEvolutions@{u_1 Lean.u_1+1.0 Lean.u_1+2.0}
    (Omega : Type)
(Job : Prosa_Behavior_Job_JobType)
(inst_3 : DecidableEq Job)
  : Type := Prosa_Results_TransferSchedulability_PaperModel_SystemEvolutions_mk
  { evo_costs : Omega ->
                Prosa_Behavior_Job_JobCost Job inst_3;
    evo_delays : Omega ->
                 Prosa_Results_TransferSchedulability_PaperModel_JobDelay Job
                   inst_3 } as default_proj_id.

Prosa_Results_TransferSchedulability_PaperModel_SystemEvolutions has primitive projections with eta conversion.
Arguments Prosa_Results_TransferSchedulability_PaperModel_SystemEvolutions Omega%_type_scope 
  Job inst_3
Arguments Prosa_Results_TransferSchedulability_PaperModel_SystemEvolutions_mk Omega%_type_scope 
  Job inst_3 (evo_costs evo_delays)%_function_scope
```
