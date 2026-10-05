# `hep_hp_ep_task`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.priority.classes.hep_hp_ep_task`
- Lean: `Prosa.Analysis.Facts.Priority.Classes.hep_hp_ep_task`
- Certificate: `hep_hp_ep_task_correspondence`

## Official Rocq

```coq
hep_hp_ep_task :
forall {Task : TaskType} {FP_policy : FP_policy Task} (tsk1 tsk2 : Equality.sort Task),
@hep_task Task FP_policy tsk1 tsk2 = @hp_task Task FP_policy tsk1 tsk2 || @ep_task Task FP_policy tsk1 tsk2

hep_hp_ep_task is not universe polymorphic
Arguments hep_hp_ep_task {Task FP_policy} tsk1 tsk2
hep_hp_ep_task is opaque
Expands to: Constant prosa.analysis.facts.priority.classes.hep_hp_ep_task
Declared in library prosa.analysis.facts.priority.classes, line 134, characters 8-22
@hep_hp_ep_task
     : forall (Task : TaskType) (FP_policy : FP_policy Task) (tsk1 tsk2 : Equality.sort Task),
       @hep_task Task FP_policy tsk1 tsk2 =
       @hp_task Task FP_policy tsk1 tsk2 || @ep_task Task FP_policy tsk1 tsk2
```

## Lean

```lean
@Prosa.Analysis.Facts.Priority.Classes.hep_hp_ep_task : ∀ {Task : Prosa.Model.Task.Concept.TaskType}
  [inst : DecidableEq Task] (FP_policy : Prosa.Model.Priority.Definitions.FP_policy Task) (tsk1 tsk2 : Task),
  Prosa.Model.Priority.Definitions.hep_task tsk1 tsk2 =
    (Prosa.Model.Priority.Definitions.hp_task tsk1 tsk2 || Prosa.Model.Priority.Definitions.ep_task tsk1 tsk2)
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Priority_Classes_hep_hp_ep_task
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (FP_policy : Prosa_Model_Priority_Definitions_FP_policy Task
                        inst_3)
         (tsk1 tsk2 : Task),
       @eq Bool
         (Prosa_Model_Priority_Definitions_FP_policy_hep_task Task
            inst_3 FP_policy tsk1 tsk2)
         (Bool_or
            (Prosa_Model_Priority_Definitions_hp_task Task
               inst_3 FP_policy tsk1 tsk2)
            (Prosa_Model_Priority_Definitions_ep_task Task
               inst_3 FP_policy tsk1 tsk2))
```
