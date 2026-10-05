# `ep_not_hp_task`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.priority.classes.ep_not_hp_task`
- Lean: `Prosa.Analysis.Facts.Priority.Classes.ep_not_hp_task`
- Certificate: `ep_not_hp_task_correspondence`

## Official Rocq

```coq
ep_not_hp_task :
forall {Task : TaskType} {FP_policy : FP_policy Task} (tsk1 tsk2 : Equality.sort Task),
is_true (@ep_task Task FP_policy tsk1 tsk2) -> is_true (~~ @hp_task Task FP_policy tsk1 tsk2)

ep_not_hp_task is not universe polymorphic
Arguments ep_not_hp_task {Task FP_policy} tsk1 tsk2 _
ep_not_hp_task is opaque
Expands to: Constant prosa.analysis.facts.priority.classes.ep_not_hp_task
Declared in library prosa.analysis.facts.priority.classes, line 115, characters 8-22
@ep_not_hp_task
     : forall (Task : TaskType) (FP_policy : FP_policy Task) (tsk1 tsk2 : Equality.sort Task),
       is_true (@ep_task Task FP_policy tsk1 tsk2) -> is_true (~~ @hp_task Task FP_policy tsk1 tsk2)
```

## Lean

```lean
@Prosa.Analysis.Facts.Priority.Classes.ep_not_hp_task : ∀ {Task : Prosa.Model.Task.Concept.TaskType}
  [inst : DecidableEq Task] (FP_policy : Prosa.Model.Priority.Definitions.FP_policy Task) (tsk1 tsk2 : Task),
  Prosa.Model.Priority.Definitions.ep_task tsk1 tsk2 = true →
    (!Prosa.Model.Priority.Definitions.hp_task tsk1 tsk2) = true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Priority_Classes_ep_not_hp_task
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (FP_policy : Prosa_Model_Priority_Definitions_FP_policy Task
                        inst_3)
         (tsk1 tsk2 : Task),
       @eq Bool
         (Prosa_Model_Priority_Definitions_ep_task Task
            inst_3 FP_policy tsk1 tsk2)
         Bool_true ->
       @eq Bool
         (Bool_not
            (Prosa_Model_Priority_Definitions_hp_task Task
               inst_3 FP_policy tsk1 tsk2))
         Bool_true
```
