# `FP_policy`

- Kind (Rocq): Class
- Rocq: `prosa.model.priority.definitions.FP_policy`
- Lean: `Prosa.Model.Priority.Definitions.FP_policy`
- Certificate: `pd_fp_import_certificate, pd_fp_export_certificate`

## Official Rocq

```coq
FP_policy : TaskType -> Type

FP_policy is not universe polymorphic
Arguments FP_policy Task
FP_policy is transparent
Expands to: Constant prosa.model.priority.definitions.FP_policy
Declared in library prosa.model.priority.definitions, line 15, characters 0-56
FP_policy
     : TaskType -> Type
```

## Lean

```lean
Prosa.Model.Priority.Definitions.FP_policy : (Task : Prosa.Model.Task.Concept.TaskType) → [DecidableEq Task] → Type u_1
```

## Lean, imported into Rocq

```coq
Prosa_Model_Priority_Definitions_FP_policy
     : forall Task : Prosa_Model_Task_Concept_TaskType, DecidableEq Task -> Type
```
