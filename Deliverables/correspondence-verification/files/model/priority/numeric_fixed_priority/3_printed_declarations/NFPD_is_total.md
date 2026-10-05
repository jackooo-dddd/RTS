# `NFPD_is_total`

- Kind (Rocq): Lemma
- Rocq: `prosa.model.priority.numeric_fixed_priority.NFPD_is_total`
- Lean: `Prosa.Model.Priority.NumericFixedPriority.NFPD_is_total`
- Certificate: `NFPD_is_total_correspondence`

## Official Rocq

```coq
NFPD_is_total :
forall {Task : TaskType} {H : TaskPriority Task}, @total_task_priorities Task (@NumericFPDescending Task H)

NFPD_is_total is not universe polymorphic
Arguments NFPD_is_total {Task H} x y
NFPD_is_total is opaque
Expands to: Constant prosa.model.priority.numeric_fixed_priority.NFPD_is_total
Declared in library prosa.model.priority.numeric_fixed_priority, line 90, characters 8-21
@NFPD_is_total
     : forall (Task : TaskType) (H : TaskPriority Task),
       @total_task_priorities Task (@NumericFPDescending Task H)
```

## Lean

```lean
@Prosa.Model.Priority.NumericFixedPriority.NFPD_is_total : ∀ {Task : Prosa.Model.Task.Concept.TaskType}
  [inst : DecidableEq Task] [inst_1 : Prosa.Model.Priority.NumericFixedPriority.TaskPriority Task],
  Prosa.Model.Priority.Definitions.total_task_priorities
    (Prosa.Model.Priority.NumericFixedPriority.NumericFPDescending Task)
```

## Lean, imported into Rocq

```coq
Prosa_Model_Priority_NumericFixedPriority_NFPD_is_total
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (inst_6 : 
          Prosa_Model_Priority_NumericFixedPriority_TaskPriority Task
            inst_3),
       Prosa_Model_Priority_Definitions_total_task_priorities Task
         inst_3
         (Prosa_Model_Priority_NumericFixedPriority_NumericFPDescending Task
            inst_3
            inst_6)
```
