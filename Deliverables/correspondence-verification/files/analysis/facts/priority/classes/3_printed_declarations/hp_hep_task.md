# `hp_hep_task`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.priority.classes.hp_hep_task`
- Lean: `Prosa.Analysis.Facts.Priority.Classes.hp_hep_task`
- Certificate: `hp_hep_task_correspondence`

## Official Rocq

```coq
hp_hep_task :
forall {Task : TaskType} {FP_policy : FP_policy Task} (tsk1 tsk2 : Equality.sort Task),
is_true (@hp_task Task FP_policy tsk1 tsk2) -> is_true (@hep_task Task FP_policy tsk1 tsk2)

hp_hep_task is not universe polymorphic
Arguments hp_hep_task {Task FP_policy} tsk1 tsk2 _
hp_hep_task is opaque
Expands to: Constant prosa.analysis.facts.priority.classes.hp_hep_task
Declared in library prosa.analysis.facts.priority.classes, line 99, characters 8-19
@hp_hep_task
     : forall (Task : TaskType) (FP_policy : FP_policy Task) (tsk1 tsk2 : Equality.sort Task),
       is_true (@hp_task Task FP_policy tsk1 tsk2) -> is_true (@hep_task Task FP_policy tsk1 tsk2)
```

## Lean

```lean
@Prosa.Analysis.Facts.Priority.Classes.hp_hep_task : ∀ {Task : Prosa.Model.Task.Concept.TaskType}
  [inst : DecidableEq Task] (FP_policy : Prosa.Model.Priority.Definitions.FP_policy Task) (tsk1 tsk2 : Task),
  Prosa.Model.Priority.Definitions.hp_task tsk1 tsk2 = true → Prosa.Model.Priority.Definitions.hep_task tsk1 tsk2 = true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Priority_Classes_hp_hep_task
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (FP_policy : Prosa_Model_Priority_Definitions_FP_policy Task
                        inst_3)
         (tsk1 tsk2 : Task),
       @eq Bool
         (Prosa_Model_Priority_Definitions_hp_task Task
            inst_3 FP_policy tsk1 tsk2)
         Bool_true ->
       @eq Bool
         (Prosa_Model_Priority_Definitions_FP_policy_hep_task Task
            inst_3 FP_policy tsk1 tsk2)
         Bool_true
```
