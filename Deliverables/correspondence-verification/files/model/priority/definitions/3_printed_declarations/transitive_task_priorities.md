# `transitive_task_priorities`

- Kind (Rocq): Definition
- Rocq: `prosa.model.priority.definitions.transitive_task_priorities`
- Lean: `Prosa.Model.Priority.Definitions.transitive_task_priorities`
- Certificate: `pd_transitive_task_priorities_certificate`

## Official Rocq

```coq
transitive_task_priorities : forall {Task : TaskType}, FP_policy Task -> Prop

transitive_task_priorities is not universe polymorphic
Arguments transitive_task_priorities {Task} FP
transitive_task_priorities is transparent
Expands to: Constant prosa.model.priority.definitions.transitive_task_priorities
Declared in library prosa.model.priority.definitions, line 136, characters 15-41
@transitive_task_priorities
     : forall Task : TaskType, FP_policy Task -> Prop
```

Body:

```coq
transitive_task_priorities =
fun (Task : TaskType) (FP : FP_policy Task) => @transitive (Equality.sort Task) (@hep_task Task FP)
     : forall {Task : TaskType}, FP_policy Task -> Prop

Arguments transitive_task_priorities {Task} FP
```

## Lean

```lean
@Prosa.Model.Priority.Definitions.transitive_task_priorities : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] → Prosa.Model.Priority.Definitions.FP_policy Task → Prop
def Prosa.Model.Priority.Definitions.transitive_task_priorities.{u_1} : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] → Prosa.Model.Priority.Definitions.FP_policy Task → Prop :=
fun {Task} [DecidableEq Task] FP =>
  ∀ (y x z : Task),
    Prosa.Model.Priority.Definitions.hep_task x y = true →
      Prosa.Model.Priority.Definitions.hep_task y z = true → Prosa.Model.Priority.Definitions.hep_task x z = true
```

## Lean, imported into Rocq

```coq
Prosa_Model_Priority_Definitions_transitive_task_priorities
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Priority_Definitions_FP_policy Task
         inst_3 ->
       SProp
```

Body:

```coq
Prosa_Model_Priority_Definitions_transitive_task_priorities@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_3 : DecidableEq Task)
  (FP : Prosa_Model_Priority_Definitions_FP_policy Task
          inst_3) =>
forall y x z : Task,
@eq Bool
  (Prosa_Model_Priority_Definitions_FP_policy_hep_task Task
     inst_3 FP x y)
  Bool_true ->
@eq Bool
  (Prosa_Model_Priority_Definitions_FP_policy_hep_task Task
     inst_3 FP y z)
  Bool_true ->
@eq Bool
  (Prosa_Model_Priority_Definitions_FP_policy_hep_task Task
     inst_3 FP x z)
  Bool_true
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Priority_Definitions_FP_policy Task
         inst_3 ->
       SProp

Arguments Prosa_Model_Priority_Definitions_transitive_task_priorities Task
  inst_3 FP
```
