# `TaskSet`

- Kind (Rocq): Definition
- Rocq: `prosa.model.task.concept.TaskSet`
- Lean: `Prosa.Model.Task.Concept.TaskSet`
- Certificate: ``

## Official Rocq

```coq
TaskSet : Type -> Type

TaskSet is not universe polymorphic
Arguments TaskSet A%type_scope
TaskSet is transparent
Expands to: Constant prosa.model.task.concept.TaskSet
Declared in library prosa.model.task.concept, line 130, characters 11-18
TaskSet
     : Type -> Type
```

Body:

```coq
TaskSet = seq
     : Type -> Type

Arguments TaskSet A%type_scope
```

## Lean

```lean
Prosa.Model.Task.Concept.TaskSet : Prosa.Model.Task.Concept.TaskType → Type u_1
@[reducible] def Prosa.Model.Task.Concept.TaskSet.{u_1} : Prosa.Model.Task.Concept.TaskType → Type u_1 :=
fun Task => List Task
```

## Lean, imported into Rocq

```coq
Prosa_Model_Task_Concept_TaskSet
     : Prosa_Model_Task_Concept_TaskType -> Type
```

Body:

```coq
Prosa_Model_Task_Concept_TaskSet@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun Task : Prosa_Model_Task_Concept_TaskType => List Task
     : Prosa_Model_Task_Concept_TaskType -> Type

Arguments Prosa_Model_Task_Concept_TaskSet Task
```
