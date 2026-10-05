# `TDMAPolicy`

- Kind (Rocq): Class
- Rocq: `prosa.model.schedule.tdma.TDMAPolicy`
- Lean: `Prosa.Model.Schedule.Tdma.TDMAPolicy`
- Certificate: `tdma_policy_source_total, tdma_policy_target_total`

## Official Rocq

```coq
TDMAPolicy : TaskType -> Type

TDMAPolicy is not universe polymorphic
Arguments TDMAPolicy T
Expands to: Inductive prosa.model.schedule.tdma.TDMAPolicy
Declared in library prosa.model.schedule.tdma, line 38, characters 6-16
TDMAPolicy
     : TaskType -> Type
```

## Lean

```lean
Prosa.Model.Schedule.Tdma.TDMAPolicy : (Task : Prosa.Model.Task.Concept.TaskType) → [DecidableEq Task] → Type u_1
```

## Lean, imported into Rocq

```coq
Prosa_Model_Schedule_Tdma_TDMAPolicy
     : forall Task : Prosa_Model_Task_Concept_TaskType, DecidableEq Task -> Type
```
