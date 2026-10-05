# `ep_task`

- Kind (Rocq): Definition
- Rocq: `prosa.model.priority.definitions.ep_task`
- Lean: `Prosa.Model.Priority.Definitions.ep_task`
- Certificate: `pd_ep_task_certificate`

## Official Rocq

```coq
ep_task : forall {Task : TaskType}, FP_policy Task -> Equality.sort Task -> Equality.sort Task -> bool

ep_task is not universe polymorphic
Arguments ep_task {Task FP_policy} tsk1 tsk2
ep_task is transparent
Expands to: Constant prosa.model.priority.definitions.ep_task
Declared in library prosa.model.priority.definitions, line 203, characters 13-20
@ep_task
     : forall Task : TaskType, FP_policy Task -> Equality.sort Task -> Equality.sort Task -> bool
```

Body:

```coq
ep_task =
fun (Task : TaskType) (FP_policy : FP_policy Task) (tsk1 tsk2 : Equality.sort Task) =>
@hep_task Task FP_policy tsk1 tsk2 && @hep_task Task FP_policy tsk2 tsk1
     : forall {Task : TaskType}, FP_policy Task -> Equality.sort Task -> Equality.sort Task -> bool

Arguments ep_task {Task FP_policy} tsk1 tsk2
```

## Lean

```lean
@Prosa.Model.Priority.Definitions.ep_task : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] → {FP : Prosa.Model.Priority.Definitions.FP_policy Task} → Task → Task → Bool
def Prosa.Model.Priority.Definitions.ep_task.{u_1} : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] → {FP : Prosa.Model.Priority.Definitions.FP_policy Task} → Task → Task → Bool :=
fun {Task} [DecidableEq Task] {FP} tsk1 tsk2 =>
  Prosa.Model.Priority.Definitions.hep_task tsk1 tsk2 && Prosa.Model.Priority.Definitions.hep_task tsk2 tsk1
```

## Lean, imported into Rocq

```coq
Prosa_Model_Priority_Definitions_ep_task
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Priority_Definitions_FP_policy Task
         inst_3 ->
       Task -> Task -> Bool
```

Body:

```coq
Prosa_Model_Priority_Definitions_ep_task@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_3 : DecidableEq Task)
  (FP : Prosa_Model_Priority_Definitions_FP_policy Task
          inst_3)
  (tsk1 tsk2 : Task) =>
Bool_and
  (Prosa_Model_Priority_Definitions_FP_policy_hep_task Task
     inst_3 FP tsk1 tsk2)
  (Prosa_Model_Priority_Definitions_FP_policy_hep_task Task
     inst_3 FP tsk2 tsk1)
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Priority_Definitions_FP_policy Task
         inst_3 ->
       Task -> Task -> Bool

Arguments Prosa_Model_Priority_Definitions_ep_task Task
  inst_3 self a____at____internal__hyg0
  a____at____internal__hyg0
```
