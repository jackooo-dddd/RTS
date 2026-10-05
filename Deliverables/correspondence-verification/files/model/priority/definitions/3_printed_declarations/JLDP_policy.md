# `JLDP_policy`

- Kind (Rocq): Class
- Rocq: `prosa.model.priority.definitions.JLDP_policy`
- Lean: `Prosa.Model.Priority.Definitions.JLDP_policy`
- Certificate: `pd_jldp_import_certificate, pd_jldp_export_certificate`

## Official Rocq

```coq
JLDP_policy : JobType -> Type

JLDP_policy is not universe polymorphic
Arguments JLDP_policy Job
JLDP_policy is transparent
Expands to: Constant prosa.model.priority.definitions.JLDP_policy
Declared in library prosa.model.priority.definitions, line 21, characters 0-68
JLDP_policy
     : JobType -> Type
```

## Lean

```lean
Prosa.Model.Priority.Definitions.JLDP_policy : (Job : Prosa.Behavior.Job.JobType) → [DecidableEq Job] → Type u_1
```

## Lean, imported into Rocq

```coq
Prosa_Model_Priority_Definitions_JLDP_policy
     : forall Job : Prosa_Behavior_Job_JobType, DecidableEq Job -> Type
```
