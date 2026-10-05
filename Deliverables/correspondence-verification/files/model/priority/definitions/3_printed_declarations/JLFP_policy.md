# `JLFP_policy`

- Kind (Rocq): Class
- Rocq: `prosa.model.priority.definitions.JLFP_policy`
- Lean: `Prosa.Model.Priority.Definitions.JLFP_policy`
- Certificate: `pd_jlfp_import_certificate, pd_jlfp_export_certificate`

## Official Rocq

```coq
JLFP_policy : JobType -> Type

JLFP_policy is not universe polymorphic
Arguments JLFP_policy Job
JLFP_policy is transparent
Expands to: Constant prosa.model.priority.definitions.JLFP_policy
Declared in library prosa.model.priority.definitions, line 18, characters 0-54
JLFP_policy
     : JobType -> Type
```

## Lean

```lean
Prosa.Model.Priority.Definitions.JLFP_policy : (Job : Prosa.Behavior.Job.JobType) → [DecidableEq Job] → Type u_1
```

## Lean, imported into Rocq

```coq
Prosa_Model_Priority_Definitions_JLFP_policy
     : forall Job : Prosa_Behavior_Job_JobType, DecidableEq Job -> Type
```
