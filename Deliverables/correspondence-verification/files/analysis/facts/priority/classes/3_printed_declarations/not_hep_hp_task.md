# `not_hep_hp_task`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.priority.classes.not_hep_hp_task`
- Lean: `Prosa.Analysis.Facts.Priority.Classes.not_hep_hp_task`
- Certificate: `not_hep_hp_task_correspondence`

## Official Rocq

```coq
not_hep_hp_task :
forall {Task : TaskType} {FP_policy : FP_policy Task},
@total (Equality.sort Task) (@hep_task Task FP_policy) ->
forall tsk1 tsk2 : Equality.sort Task,
~~ @hep_task Task FP_policy tsk1 tsk2 = @hp_task Task FP_policy tsk2 tsk1

not_hep_hp_task is not universe polymorphic
Arguments not_hep_hp_task {Task FP_policy} H_total tsk1 tsk2
not_hep_hp_task is opaque
Expands to: Constant prosa.analysis.facts.priority.classes.not_hep_hp_task
Declared in library prosa.analysis.facts.priority.classes, line 207, characters 10-25
@not_hep_hp_task
     : forall (Task : TaskType) (FP_policy : FP_policy Task),
       @total (Equality.sort Task) (@hep_task Task FP_policy) ->
       forall tsk1 tsk2 : Equality.sort Task,
       ~~ @hep_task Task FP_policy tsk1 tsk2 = @hp_task Task FP_policy tsk2 tsk1
```

## Lean

```lean
@Prosa.Analysis.Facts.Priority.Classes.not_hep_hp_task : ∀ {Task : Prosa.Model.Task.Concept.TaskType}
  [inst : DecidableEq Task] (FP_policy : Prosa.Model.Priority.Definitions.FP_policy Task),
  (∀ (x y : Task),
      (Prosa.Model.Priority.Definitions.hep_task x y || Prosa.Model.Priority.Definitions.hep_task y x) = true) →
    ∀ (tsk1 tsk2 : Task),
      (!Prosa.Model.Priority.Definitions.hep_task tsk1 tsk2) = Prosa.Model.Priority.Definitions.hp_task tsk2 tsk1
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Priority_Classes_not_hep_hp_task
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (FP_policy : Prosa_Model_Priority_Definitions_FP_policy Task
                        inst_3),
       (forall x y : Task,
        @eq Bool
          (Bool_or
             (Prosa_Model_Priority_Definitions_FP_policy_hep_task Task
                inst_3 FP_policy x y)
             (Prosa_Model_Priority_Definitions_FP_policy_hep_task Task
                inst_3 FP_policy y x))
          Bool_true) ->
       forall tsk1 tsk2 : Task,
       @eq Bool
         (Bool_not
            (Prosa_Model_Priority_Definitions_FP_policy_hep_task Task
               inst_3 FP_policy tsk1 tsk2))
         (Prosa_Model_Priority_Definitions_hp_task Task
            inst_3 FP_policy tsk2 tsk1)
```
