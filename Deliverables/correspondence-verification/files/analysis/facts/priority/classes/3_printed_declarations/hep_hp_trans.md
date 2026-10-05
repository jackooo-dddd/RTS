# `hep_hp_trans`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.priority.classes.hep_hp_trans`
- Lean: `Prosa.Analysis.Facts.Priority.Classes.hep_hp_trans`
- Certificate: `hep_hp_trans_correspondence`

## Official Rocq

```coq
hep_hp_trans :
forall {Task : TaskType} {FP_policy : FP_policy Task},
@transitive (Equality.sort Task) (@hep_task Task FP_policy) ->
forall tsk1 tsk2 tsk3 : Equality.sort Task,
is_true (@hep_task Task FP_policy tsk1 tsk2) ->
is_true (@hp_task Task FP_policy tsk2 tsk3) -> is_true (@hp_task Task FP_policy tsk1 tsk3)

hep_hp_trans is not universe polymorphic
Arguments hep_hp_trans {Task FP_policy} H_transitive tsk1 tsk2 tsk3 _ _
hep_hp_trans is opaque
Expands to: Constant prosa.analysis.facts.priority.classes.hep_hp_trans
Declared in library prosa.analysis.facts.priority.classes, line 185, characters 10-22
@hep_hp_trans
     : forall (Task : TaskType) (FP_policy : FP_policy Task),
       @transitive (Equality.sort Task) (@hep_task Task FP_policy) ->
       forall tsk1 tsk2 tsk3 : Equality.sort Task,
       is_true (@hep_task Task FP_policy tsk1 tsk2) ->
       is_true (@hp_task Task FP_policy tsk2 tsk3) -> is_true (@hp_task Task FP_policy tsk1 tsk3)
```

## Lean

```lean
@Prosa.Analysis.Facts.Priority.Classes.hep_hp_trans : ∀ {Task : Prosa.Model.Task.Concept.TaskType}
  [inst : DecidableEq Task] (FP_policy : Prosa.Model.Priority.Definitions.FP_policy Task),
  (∀ (y x z : Task),
      Prosa.Model.Priority.Definitions.hep_task x y = true →
        Prosa.Model.Priority.Definitions.hep_task y z = true → Prosa.Model.Priority.Definitions.hep_task x z = true) →
    ∀ (tsk1 tsk2 tsk3 : Task),
      Prosa.Model.Priority.Definitions.hep_task tsk1 tsk2 = true →
        Prosa.Model.Priority.Definitions.hp_task tsk2 tsk3 = true →
          Prosa.Model.Priority.Definitions.hp_task tsk1 tsk3 = true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Priority_Classes_hep_hp_trans
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (FP_policy : Prosa_Model_Priority_Definitions_FP_policy Task
                        inst_3),
       (forall y x z : Task,
        @eq Bool
          (Prosa_Model_Priority_Definitions_FP_policy_hep_task Task
             inst_3 FP_policy x y)
          Bool_true ->
        @eq Bool
          (Prosa_Model_Priority_Definitions_FP_policy_hep_task Task
             inst_3 FP_policy y z)
          Bool_true ->
        @eq Bool
          (Prosa_Model_Priority_Definitions_FP_policy_hep_task Task
             inst_3 FP_policy x z)
          Bool_true) ->
       forall tsk1 tsk2 tsk3 : Task,
       @eq Bool
         (Prosa_Model_Priority_Definitions_FP_policy_hep_task Task
            inst_3 FP_policy tsk1 tsk2)
         Bool_true ->
       @eq Bool
         (Prosa_Model_Priority_Definitions_hp_task Task
            inst_3 FP_policy tsk2 tsk3)
         Bool_true ->
       @eq Bool
         (Prosa_Model_Priority_Definitions_hp_task Task
            inst_3 FP_policy tsk1 tsk3)
         Bool_true
```
