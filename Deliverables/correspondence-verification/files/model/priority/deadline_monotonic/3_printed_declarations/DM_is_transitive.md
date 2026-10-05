# `DM_is_transitive`

- Kind (Rocq): Lemma
- Rocq: `prosa.model.priority.deadline_monotonic.DM_is_transitive`
- Lean: `Prosa.Model.Priority.DeadlineMonotonic.DM_is_transitive`
- Certificate: `DM_is_transitive_correspondence`

## Official Rocq

```coq
DM_is_transitive :
forall {Task : TaskType} {H : TaskDeadline Task}, @transitive_task_priorities Task (@DM Task H)

DM_is_transitive is not universe polymorphic
Arguments DM_is_transitive {Task H} y x z _ _
DM_is_transitive is opaque
Expands to: Constant prosa.model.priority.deadline_monotonic.DM_is_transitive
Declared in library prosa.model.priority.deadline_monotonic, line 29, characters 8-24
@DM_is_transitive
     : forall (Task : TaskType) (H : TaskDeadline Task), @transitive_task_priorities Task (@DM Task H)
```

## Lean

```lean
@Prosa.Model.Priority.DeadlineMonotonic.DM_is_transitive : ∀ {Task : Prosa.Model.Task.Concept.TaskType}
  [inst : DecidableEq Task] [inst_1 : Prosa.Model.Task.Concept.TaskDeadline Task],
  Prosa.Model.Priority.Definitions.transitive_task_priorities (Prosa.Model.Priority.DeadlineMonotonic.DM Task)
```

## Lean, imported into Rocq

```coq
Prosa_Model_Priority_DeadlineMonotonic_DM_is_transitive
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (inst_6 : 
          Prosa_Model_Task_Concept_TaskDeadline Task
            inst_3),
       Prosa_Model_Priority_Definitions_transitive_task_priorities Task
         inst_3
         (Prosa_Model_Priority_DeadlineMonotonic_DM Task
            inst_3
            inst_6)
```
