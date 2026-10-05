# `ep_task_sym`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.priority.classes.ep_task_sym`
- Lean: `Prosa.Analysis.Facts.Priority.Classes.ep_task_sym`
- Certificate: `ep_task_sym_correspondence`

## Official Rocq

```coq
ep_task_sym :
forall {Task : TaskType} {FP_policy : FP_policy Task} (tsk1 tsk2 : Equality.sort Task),
@ep_task Task FP_policy tsk1 tsk2 = @ep_task Task FP_policy tsk2 tsk1

ep_task_sym is not universe polymorphic
Arguments ep_task_sym {Task FP_policy} tsk1 tsk2
ep_task_sym is opaque
Expands to: Constant prosa.analysis.facts.priority.classes.ep_task_sym
Declared in library prosa.analysis.facts.priority.classes, line 126, characters 8-19
@ep_task_sym
     : forall (Task : TaskType) (FP_policy : FP_policy Task) (tsk1 tsk2 : Equality.sort Task),
       @ep_task Task FP_policy tsk1 tsk2 = @ep_task Task FP_policy tsk2 tsk1
```

## Lean

```lean
@Prosa.Analysis.Facts.Priority.Classes.ep_task_sym : ∀ {Task : Prosa.Model.Task.Concept.TaskType}
  [inst : DecidableEq Task] (FP_policy : Prosa.Model.Priority.Definitions.FP_policy Task) (tsk1 tsk2 : Task),
  Prosa.Model.Priority.Definitions.ep_task tsk1 tsk2 = Prosa.Model.Priority.Definitions.ep_task tsk2 tsk1
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Priority_Classes_ep_task_sym
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (FP_policy : Prosa_Model_Priority_Definitions_FP_policy Task
                        inst_3)
         (tsk1 tsk2 : Task),
       @eq Bool
         (Prosa_Model_Priority_Definitions_ep_task Task
            inst_3 FP_policy tsk1 tsk2)
         (Prosa_Model_Priority_Definitions_ep_task Task
            inst_3 FP_policy tsk2 tsk1)
```
