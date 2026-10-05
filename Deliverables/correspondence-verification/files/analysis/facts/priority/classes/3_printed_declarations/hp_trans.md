# `hp_trans`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.priority.classes.hp_trans`
- Lean: `Prosa.Analysis.Facts.Priority.Classes.hp_trans`
- Certificate: `hp_trans_correspondence`

## Official Rocq

```coq
hp_trans :
forall {Task : TaskType} {FP_policy : FP_policy Task},
@transitive (Equality.sort Task) (@hep_task Task FP_policy) ->
@transitive (Equality.sort Task) (@hp_task Task FP_policy)

hp_trans is not universe polymorphic
Arguments hp_trans {Task FP_policy} H_transitive y x z _ _
hp_trans is opaque
Expands to: Constant prosa.analysis.facts.priority.classes.hp_trans
Declared in library prosa.analysis.facts.priority.classes, line 161, characters 10-18
@hp_trans
     : forall (Task : TaskType) (FP_policy : FP_policy Task),
       @transitive (Equality.sort Task) (@hep_task Task FP_policy) ->
       @transitive (Equality.sort Task) (@hp_task Task FP_policy)
```

## Lean

```lean
@Prosa.Analysis.Facts.Priority.Classes.hp_trans : ∀ {Task : Prosa.Model.Task.Concept.TaskType} [inst : DecidableEq Task]
  (FP_policy : Prosa.Model.Priority.Definitions.FP_policy Task),
  (∀ (y x z : Task),
      Prosa.Model.Priority.Definitions.hep_task x y = true →
        Prosa.Model.Priority.Definitions.hep_task y z = true → Prosa.Model.Priority.Definitions.hep_task x z = true) →
    ∀ (y x z : Task),
      Prosa.Model.Priority.Definitions.hp_task x y = true →
        Prosa.Model.Priority.Definitions.hp_task y z = true → Prosa.Model.Priority.Definitions.hp_task x z = true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Priority_Classes_hp_trans
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
       forall y x z : Task,
       @eq Bool
         (Prosa_Model_Priority_Definitions_hp_task Task
            inst_3 FP_policy x y)
         Bool_true ->
       @eq Bool
         (Prosa_Model_Priority_Definitions_hp_task Task
            inst_3 FP_policy y z)
         Bool_true ->
       @eq Bool
         (Prosa_Model_Priority_Definitions_hp_task Task
            inst_3 FP_policy x z)
         Bool_true
```
