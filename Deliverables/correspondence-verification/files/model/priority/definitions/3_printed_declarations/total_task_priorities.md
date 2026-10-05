# `total_task_priorities`

- Kind (Rocq): Definition
- Rocq: `prosa.model.priority.definitions.total_task_priorities`
- Lean: `Prosa.Model.Priority.Definitions.total_task_priorities`
- Certificate: `pd_total_task_priorities_certificate`

## Official Rocq

```coq
total_task_priorities : forall {Task : TaskType}, FP_policy Task -> Prop

total_task_priorities is not universe polymorphic
Arguments total_task_priorities {Task} FP
total_task_priorities is transparent
Expands to: Constant prosa.model.priority.definitions.total_task_priorities
Declared in library prosa.model.priority.definitions, line 139, characters 15-36
@total_task_priorities
     : forall Task : TaskType, FP_policy Task -> Prop
```

Body:

```coq
total_task_priorities =
fun (Task : TaskType) (FP : FP_policy Task) => @total (Equality.sort Task) (@hep_task Task FP)
     : forall {Task : TaskType}, FP_policy Task -> Prop

Arguments total_task_priorities {Task} FP
```

## Lean

```lean
@Prosa.Model.Priority.Definitions.total_task_priorities : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] → Prosa.Model.Priority.Definitions.FP_policy Task → Prop
def Prosa.Model.Priority.Definitions.total_task_priorities.{u_1} : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] → Prosa.Model.Priority.Definitions.FP_policy Task → Prop :=
fun {Task} [DecidableEq Task] FP =>
  ∀ (x y : Task),
    (Prosa.Model.Priority.Definitions.hep_task x y || Prosa.Model.Priority.Definitions.hep_task y x) = true
```

## Lean, imported into Rocq

```coq
Prosa_Model_Priority_Definitions_total_task_priorities
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Priority_Definitions_FP_policy Task
         inst_3 ->
       SProp
```

Body:

```coq
Prosa_Model_Priority_Definitions_total_task_priorities@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_3 : DecidableEq Task)
  (FP : Prosa_Model_Priority_Definitions_FP_policy Task
          inst_3) =>
forall x y : Task,
@eq Bool
  (Bool_or
     (Prosa_Model_Priority_Definitions_FP_policy_hep_task Task
        inst_3 FP x y)
     (Prosa_Model_Priority_Definitions_FP_policy_hep_task Task
        inst_3 FP y x))
  Bool_true
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Priority_Definitions_FP_policy Task
         inst_3 ->
       SProp

Arguments Prosa_Model_Priority_Definitions_total_task_priorities Task
  inst_3 FP
```
