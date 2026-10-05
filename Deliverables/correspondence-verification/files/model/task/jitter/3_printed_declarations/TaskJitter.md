# `TaskJitter`

- Kind (Rocq): Class
- Rocq: `prosa.model.task.jitter.TaskJitter`
- Lean: `Prosa.Model.Task.Jitter.TaskJitter`
- Certificate: `TaskJitter_source_total, TaskJitter_target_total, TaskJitter_source_roundtrip`

## Official Rocq

```coq
TaskJitter : TaskType -> Type

TaskJitter is not universe polymorphic
Arguments TaskJitter Task
TaskJitter is transparent
Expands to: Constant prosa.model.task.jitter.TaskJitter
Declared in library prosa.model.task.jitter, line 8, characters 0-69
TaskJitter
     : TaskType -> Type
```

## Lean

```lean
Prosa.Model.Task.Jitter.TaskJitter : (Task : Prosa.Model.Task.Concept.TaskType) → [DecidableEq Task] → Type u_1
```

## Lean, imported into Rocq

```coq
Prosa_Model_Task_Jitter_TaskJitter
     : forall Task : Prosa_Model_Task_Concept_TaskType, DecidableEq Task -> Type
```
