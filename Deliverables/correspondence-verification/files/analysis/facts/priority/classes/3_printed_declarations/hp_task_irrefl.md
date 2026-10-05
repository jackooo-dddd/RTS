# `hp_task_irrefl`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.priority.classes.hp_task_irrefl`
- Lean: `Prosa.Analysis.Facts.Priority.Classes.hp_task_irrefl`
- Certificate: `hp_task_irrefl_correspondence`

## Official Rocq

```coq
hp_task_irrefl :
forall {Task : TaskType} {FP_policy : FP_policy Task},
@irreflexive (Equality.sort Task) (@hp_task Task FP_policy)

hp_task_irrefl is not universe polymorphic
Arguments hp_task_irrefl {Task FP_policy} x
hp_task_irrefl is opaque
Expands to: Constant prosa.analysis.facts.priority.classes.hp_task_irrefl
Declared in library prosa.analysis.facts.priority.classes, line 94, characters 8-22
@hp_task_irrefl
     : forall (Task : TaskType) (FP_policy : FP_policy Task),
       @irreflexive (Equality.sort Task) (@hp_task Task FP_policy)
```

## Lean

```lean
@Prosa.Analysis.Facts.Priority.Classes.hp_task_irrefl : ∀ {Task : Prosa.Model.Task.Concept.TaskType}
  [inst : DecidableEq Task] (FP_policy : Prosa.Model.Priority.Definitions.FP_policy Task) (tsk : Task),
  Prosa.Model.Priority.Definitions.hp_task tsk tsk = false
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Priority_Classes_hp_task_irrefl
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (FP_policy : Prosa_Model_Priority_Definitions_FP_policy Task
                        inst_3)
         (tsk : Task),
       @eq Bool
         (Prosa_Model_Priority_Definitions_hp_task Task
            inst_3 FP_policy tsk tsk)
         Bool_false
```
