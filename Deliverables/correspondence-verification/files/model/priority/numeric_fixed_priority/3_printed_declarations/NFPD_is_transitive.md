# `NFPD_is_transitive`

- Kind (Rocq): Lemma
- Rocq: `prosa.model.priority.numeric_fixed_priority.NFPD_is_transitive`
- Lean: `Prosa.Model.Priority.NumericFixedPriority.NFPD_is_transitive`
- Certificate: `NFPD_is_transitive_correspondence`

## Official Rocq

```coq
NFPD_is_transitive :
forall {Task : TaskType} {H : TaskPriority Task},
@transitive_task_priorities Task (@NumericFPDescending Task H)

NFPD_is_transitive is not universe polymorphic
Arguments NFPD_is_transitive {Task H} y x z _ _
NFPD_is_transitive is opaque
Expands to: Constant prosa.model.priority.numeric_fixed_priority.NFPD_is_transitive
Declared in library prosa.model.priority.numeric_fixed_priority, line 83, characters 8-26
@NFPD_is_transitive
     : forall (Task : TaskType) (H : TaskPriority Task),
       @transitive_task_priorities Task (@NumericFPDescending Task H)
```

## Lean

```lean
@Prosa.Model.Priority.NumericFixedPriority.NFPD_is_transitive : ∀ {Task : Prosa.Model.Task.Concept.TaskType}
  [inst : DecidableEq Task] [inst_1 : Prosa.Model.Priority.NumericFixedPriority.TaskPriority Task],
  Prosa.Model.Priority.Definitions.transitive_task_priorities
    (Prosa.Model.Priority.NumericFixedPriority.NumericFPDescending Task)
```

## Lean, imported into Rocq

```coq
Prosa_Model_Priority_NumericFixedPriority_NFPD_is_transitive
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (inst_6 : 
          Prosa_Model_Priority_NumericFixedPriority_TaskPriority Task
            inst_3),
       Prosa_Model_Priority_Definitions_transitive_task_priorities Task
         inst_3
         (Prosa_Model_Priority_NumericFixedPriority_NumericFPDescending Task
            inst_3
            inst_6)
```
