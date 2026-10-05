# `TaskType`

- Kind (Rocq): Definition
- Rocq: `prosa.model.task.concept.TaskType`
- Lean: `Prosa.Model.Task.Concept.TaskType`
- Certificate: ``

## Official Rocq

```coq
TaskType : Type

TaskType is not universe polymorphic
TaskType is transparent
Expands to: Constant prosa.model.task.concept.TaskType
Declared in library prosa.model.task.concept, line 10, characters 11-19
TaskType
     : Type
```

Body:

```coq
TaskType = eqType
     : Type
```

## Lean

```lean
Prosa.Model.Task.Concept.TaskType : Type (u_1 + 1)
@[reducible] def Prosa.Model.Task.Concept.TaskType.{u} : Type (u + 1) :=
Type u
```

## Lean, imported into Rocq

```coq
Prosa_Model_Task_Concept_TaskType
     : Type
```

Body:

```coq
Prosa_Model_Task_Concept_TaskType@{u Lean.u+1.0 Lean.u+2.0} = Type
     : Type
```
