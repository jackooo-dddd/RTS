# `hp_task`

- Kind (Rocq): Definition
- Rocq: `prosa.model.priority.definitions.hp_task`
- Lean: `Prosa.Model.Priority.Definitions.hp_task`
- Certificate: `pd_hp_task_certificate`

## Official Rocq

```coq
hp_task : forall {Task : TaskType}, FP_policy Task -> Equality.sort Task -> Equality.sort Task -> bool

hp_task is not universe polymorphic
Arguments hp_task {Task FP_policy} tsk1 tsk2
hp_task is transparent
Expands to: Constant prosa.model.priority.definitions.hp_task
Declared in library prosa.model.priority.definitions, line 197, characters 13-20
@hp_task
     : forall Task : TaskType, FP_policy Task -> Equality.sort Task -> Equality.sort Task -> bool
```

Body:

```coq
hp_task =
fun (Task : TaskType) (FP_policy : FP_policy Task) (tsk1 tsk2 : Equality.sort Task) =>
@hep_task Task FP_policy tsk1 tsk2 && ~~ @hep_task Task FP_policy tsk2 tsk1
     : forall {Task : TaskType}, FP_policy Task -> Equality.sort Task -> Equality.sort Task -> bool

Arguments hp_task {Task FP_policy} tsk1 tsk2
```

## Lean

```lean
@Prosa.Model.Priority.Definitions.hp_task : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] → {FP : Prosa.Model.Priority.Definitions.FP_policy Task} → Task → Task → Bool
def Prosa.Model.Priority.Definitions.hp_task.{u_1} : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] → {FP : Prosa.Model.Priority.Definitions.FP_policy Task} → Task → Task → Bool :=
fun {Task} [DecidableEq Task] {FP} tsk1 tsk2 =>
  Prosa.Model.Priority.Definitions.hep_task tsk1 tsk2 && !Prosa.Model.Priority.Definitions.hep_task tsk2 tsk1
```

## Lean, imported into Rocq

```coq
Prosa_Model_Priority_Definitions_hp_task
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Priority_Definitions_FP_policy Task
         inst_3 ->
       Task -> Task -> Bool
```

Body:

```coq
Prosa_Model_Priority_Definitions_hp_task@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_3 : DecidableEq Task)
  (FP : Prosa_Model_Priority_Definitions_FP_policy Task
          inst_3)
  (tsk1 tsk2 : Task) =>
Bool_and
  (Prosa_Model_Priority_Definitions_FP_policy_hep_task Task
     inst_3 FP tsk1 tsk2)
  (Bool_not
     (Prosa_Model_Priority_Definitions_FP_policy_hep_task Task
        inst_3 FP tsk2 tsk1))
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Priority_Definitions_FP_policy Task
         inst_3 ->
       Task -> Task -> Bool

Arguments Prosa_Model_Priority_Definitions_hp_task Task
  inst_3 self a____at____internal__hyg0
  a____at____internal__hyg0
```
