# `RM_is_transitive`

- Kind (Rocq): Lemma
- Rocq: `prosa.model.priority.rate_monotonic.RM_is_transitive`
- Lean: `Prosa.Model.Priority.RateMonotonic.RM_is_transitive`
- Certificate: `RM_is_transitive_correspondence`

## Official Rocq

```coq
RM_is_transitive :
forall {Task : TaskType} {H : SporadicModel Task}, @transitive_task_priorities Task (@RM Task H)

RM_is_transitive is not universe polymorphic
Arguments RM_is_transitive {Task H} y x z _ _
RM_is_transitive is opaque
Expands to: Constant prosa.model.priority.rate_monotonic.RM_is_transitive
Declared in library prosa.model.priority.rate_monotonic, line 31, characters 8-24
@RM_is_transitive
     : forall (Task : TaskType) (H : SporadicModel Task), @transitive_task_priorities Task (@RM Task H)
```

## Lean

```lean
@Prosa.Model.Priority.RateMonotonic.RM_is_transitive : ∀ {Task : Prosa.Model.Task.Concept.TaskType}
  [inst : DecidableEq Task] [inst_1 : Prosa.Model.Task.Arrival.Sporadic.SporadicModel Task],
  Prosa.Model.Priority.Definitions.transitive_task_priorities (Prosa.Model.Priority.RateMonotonic.RM Task)
```

## Lean, imported into Rocq

```coq
Prosa_Model_Priority_RateMonotonic_RM_is_transitive
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (inst_6 : 
          Prosa_Model_Task_Arrival_Sporadic_SporadicModel Task
            inst_3),
       Prosa_Model_Priority_Definitions_transitive_task_priorities Task
         inst_3
         (Prosa_Model_Priority_RateMonotonic_RM Task
            inst_3
            inst_6)
```
