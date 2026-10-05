# `DM_is_total`

- Kind (Rocq): Lemma
- Rocq: `prosa.model.priority.deadline_monotonic.DM_is_total`
- Lean: `Prosa.Model.Priority.DeadlineMonotonic.DM_is_total`
- Certificate: `DM_is_total_correspondence`

## Official Rocq

```coq
DM_is_total : forall {Task : TaskType} {H : TaskDeadline Task}, @total_task_priorities Task (@DM Task H)

DM_is_total is not universe polymorphic
Arguments DM_is_total {Task H} x y
DM_is_total is opaque
Expands to: Constant prosa.model.priority.deadline_monotonic.DM_is_total
Declared in library prosa.model.priority.deadline_monotonic, line 33, characters 8-19
@DM_is_total
     : forall (Task : TaskType) (H : TaskDeadline Task), @total_task_priorities Task (@DM Task H)
```

## Lean

```lean
@Prosa.Model.Priority.DeadlineMonotonic.DM_is_total : ∀ {Task : Prosa.Model.Task.Concept.TaskType}
  [inst : DecidableEq Task] [inst_1 : Prosa.Model.Task.Concept.TaskDeadline Task],
  Prosa.Model.Priority.Definitions.total_task_priorities (Prosa.Model.Priority.DeadlineMonotonic.DM Task)
```

## Lean, imported into Rocq

```coq
Prosa_Model_Priority_DeadlineMonotonic_DM_is_total
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (inst_6 : 
          Prosa_Model_Task_Concept_TaskDeadline Task
            inst_3),
       Prosa_Model_Priority_Definitions_total_task_priorities Task
         inst_3
         (Prosa_Model_Priority_DeadlineMonotonic_DM Task
            inst_3
            inst_6)
```
