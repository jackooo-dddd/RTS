# `RM_is_reflexive`

- Kind (Rocq): Lemma
- Rocq: `prosa.model.priority.rate_monotonic.RM_is_reflexive`
- Lean: `Prosa.Model.Priority.RateMonotonic.RM_is_reflexive`
- Certificate: `RM_is_reflexive_correspondence`

## Official Rocq

```coq
RM_is_reflexive :
forall {Task : TaskType} {H : SporadicModel Task}, @reflexive_task_priorities Task (@RM Task H)

RM_is_reflexive is not universe polymorphic
Arguments RM_is_reflexive {Task H} x
RM_is_reflexive is opaque
Expands to: Constant prosa.model.priority.rate_monotonic.RM_is_reflexive
Declared in library prosa.model.priority.rate_monotonic, line 27, characters 8-23
@RM_is_reflexive
     : forall (Task : TaskType) (H : SporadicModel Task), @reflexive_task_priorities Task (@RM Task H)
```

## Lean

```lean
@Prosa.Model.Priority.RateMonotonic.RM_is_reflexive : ∀ {Task : Prosa.Model.Task.Concept.TaskType}
  [inst : DecidableEq Task] [inst_1 : Prosa.Model.Task.Arrival.Sporadic.SporadicModel Task],
  Prosa.Model.Priority.Definitions.reflexive_task_priorities (Prosa.Model.Priority.RateMonotonic.RM Task)
```

## Lean, imported into Rocq

```coq
Prosa_Model_Priority_RateMonotonic_RM_is_reflexive
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (inst_6 : 
          Prosa_Model_Task_Arrival_Sporadic_SporadicModel Task
            inst_3),
       Prosa_Model_Priority_Definitions_reflexive_task_priorities Task
         inst_3
         (Prosa_Model_Priority_RateMonotonic_RM Task
            inst_3
            inst_6)
```
