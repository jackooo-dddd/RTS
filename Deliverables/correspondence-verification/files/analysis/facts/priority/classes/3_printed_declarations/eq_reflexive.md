# `eq_reflexive`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.priority.classes.eq_reflexive`
- Lean: `Prosa.Analysis.Facts.Priority.Classes.eq_reflexive`
- Certificate: `eq_reflexive_correspondence`

## Official Rocq

```coq
eq_reflexive :
forall {Task : TaskType} {FP_policy : FP_policy Task},
@reflexive (Equality.sort Task) (@hep_task Task FP_policy) ->
@reflexive (Equality.sort Task) (@ep_task Task FP_policy)

eq_reflexive is not universe polymorphic
Arguments eq_reflexive {Task FP_policy} H_reflexive x
eq_reflexive is opaque
Expands to: Constant prosa.analysis.facts.priority.classes.eq_reflexive
Declared in library prosa.analysis.facts.priority.classes, line 148, characters 10-22
@eq_reflexive
     : forall (Task : TaskType) (FP_policy : FP_policy Task),
       @reflexive (Equality.sort Task) (@hep_task Task FP_policy) ->
       @reflexive (Equality.sort Task) (@ep_task Task FP_policy)
```

## Lean

```lean
@Prosa.Analysis.Facts.Priority.Classes.eq_reflexive : ∀ {Task : Prosa.Model.Task.Concept.TaskType}
  [inst : DecidableEq Task] (FP_policy : Prosa.Model.Priority.Definitions.FP_policy Task),
  (∀ (tsk : Task), Prosa.Model.Priority.Definitions.hep_task tsk tsk = true) →
    ∀ (tsk : Task), Prosa.Model.Priority.Definitions.ep_task tsk tsk = true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Priority_Classes_eq_reflexive
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (FP_policy : Prosa_Model_Priority_Definitions_FP_policy Task
                        inst_3),
       (forall tsk : Task,
        @eq Bool
          (Prosa_Model_Priority_Definitions_FP_policy_hep_task Task
             inst_3 FP_policy tsk tsk)
          Bool_true) ->
       forall tsk : Task,
       @eq Bool
         (Prosa_Model_Priority_Definitions_ep_task Task
            inst_3 FP_policy tsk tsk)
         Bool_true
```
