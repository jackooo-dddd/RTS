# `DM_is_reflexive`

- Kind (Rocq): Lemma
- Rocq: `prosa.model.priority.deadline_monotonic.DM_is_reflexive`
- Lean: `Prosa.Model.Priority.DeadlineMonotonic.DM_is_reflexive`
- Certificate: `DM_is_reflexive_correspondence`

## Official Rocq

```coq
DM_is_reflexive :
forall {Task : TaskType} {H : TaskDeadline Task}, @reflexive_task_priorities Task (@DM Task H)

DM_is_reflexive is not universe polymorphic
Arguments DM_is_reflexive {Task H} x
DM_is_reflexive is opaque
Expands to: Constant prosa.model.priority.deadline_monotonic.DM_is_reflexive
Declared in library prosa.model.priority.deadline_monotonic, line 25, characters 8-23
@DM_is_reflexive
     : forall (Task : TaskType) (H : TaskDeadline Task), @reflexive_task_priorities Task (@DM Task H)
```

## Lean

```lean
@Prosa.Model.Priority.DeadlineMonotonic.DM_is_reflexive : ∀ {Task : Prosa.Model.Task.Concept.TaskType}
  [inst : DecidableEq Task] [inst_1 : Prosa.Model.Task.Concept.TaskDeadline Task],
  Prosa.Model.Priority.Definitions.reflexive_task_priorities (Prosa.Model.Priority.DeadlineMonotonic.DM Task)
```

## Lean, imported into Rocq

```coq
Prosa_Model_Priority_DeadlineMonotonic_DM_is_reflexive
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (inst_6 : 
          Prosa_Model_Task_Concept_TaskDeadline Task
            inst_3),
       Prosa_Model_Priority_Definitions_reflexive_task_priorities Task
         inst_3
         (Prosa_Model_Priority_DeadlineMonotonic_DM Task
            inst_3
            inst_6)
```
