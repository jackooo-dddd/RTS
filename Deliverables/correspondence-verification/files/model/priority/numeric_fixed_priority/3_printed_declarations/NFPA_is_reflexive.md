# `NFPA_is_reflexive`

- Kind (Rocq): Lemma
- Rocq: `prosa.model.priority.numeric_fixed_priority.NFPA_is_reflexive`
- Lean: `Prosa.Model.Priority.NumericFixedPriority.NFPA_is_reflexive`
- Certificate: `NFPA_is_reflexive_correspondence`

## Official Rocq

```coq
NFPA_is_reflexive :
forall {Task : TaskType} {H : TaskPriority Task},
@reflexive_task_priorities Task (@NumericFPAscending Task H)

NFPA_is_reflexive is not universe polymorphic
Arguments NFPA_is_reflexive {Task H} x
NFPA_is_reflexive is opaque
Expands to: Constant prosa.model.priority.numeric_fixed_priority.NFPA_is_reflexive
Declared in library prosa.model.priority.numeric_fixed_priority, line 42, characters 8-25
@NFPA_is_reflexive
     : forall (Task : TaskType) (H : TaskPriority Task),
       @reflexive_task_priorities Task (@NumericFPAscending Task H)
```

## Lean

```lean
@Prosa.Model.Priority.NumericFixedPriority.NFPA_is_reflexive : ∀ {Task : Prosa.Model.Task.Concept.TaskType}
  [inst : DecidableEq Task] [inst_1 : Prosa.Model.Priority.NumericFixedPriority.TaskPriority Task],
  Prosa.Model.Priority.Definitions.reflexive_task_priorities
    (Prosa.Model.Priority.NumericFixedPriority.NumericFPAscending Task)
```

## Lean, imported into Rocq

```coq
Prosa_Model_Priority_NumericFixedPriority_NFPA_is_reflexive
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (inst_6 : 
          Prosa_Model_Priority_NumericFixedPriority_TaskPriority Task
            inst_3),
       Prosa_Model_Priority_Definitions_reflexive_task_priorities Task
         inst_3
         (Prosa_Model_Priority_NumericFixedPriority_NumericFPAscending Task
            inst_3
            inst_6)
```
