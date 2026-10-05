# `RM_is_total`

- Kind (Rocq): Lemma
- Rocq: `prosa.model.priority.rate_monotonic.RM_is_total`
- Lean: `Prosa.Model.Priority.RateMonotonic.RM_is_total`
- Certificate: `RM_is_total_correspondence`

## Official Rocq

```coq
RM_is_total : forall {Task : TaskType} {H : SporadicModel Task}, @total_task_priorities Task (@RM Task H)

RM_is_total is not universe polymorphic
Arguments RM_is_total {Task H} x y
RM_is_total is opaque
Expands to: Constant prosa.model.priority.rate_monotonic.RM_is_total
Declared in library prosa.model.priority.rate_monotonic, line 35, characters 8-19
@RM_is_total
     : forall (Task : TaskType) (H : SporadicModel Task), @total_task_priorities Task (@RM Task H)
```

## Lean

```lean
@Prosa.Model.Priority.RateMonotonic.RM_is_total : ∀ {Task : Prosa.Model.Task.Concept.TaskType} [inst : DecidableEq Task]
  [inst_1 : Prosa.Model.Task.Arrival.Sporadic.SporadicModel Task],
  Prosa.Model.Priority.Definitions.total_task_priorities (Prosa.Model.Priority.RateMonotonic.RM Task)
```

## Lean, imported into Rocq

```coq
Prosa_Model_Priority_RateMonotonic_RM_is_total
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (inst_6 : 
          Prosa_Model_Task_Arrival_Sporadic_SporadicModel Task
            inst_3),
       Prosa_Model_Priority_Definitions_total_task_priorities Task
         inst_3
         (Prosa_Model_Priority_RateMonotonic_RM Task
            inst_3
            inst_6)
```
