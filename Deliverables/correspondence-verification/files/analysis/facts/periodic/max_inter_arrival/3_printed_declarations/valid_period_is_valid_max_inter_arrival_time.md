# `valid_period_is_valid_max_inter_arrival_time`

- Kind (Rocq): Remark
- Rocq: `prosa.analysis.facts.periodic.max_inter_arrival.valid_period_is_valid_max_inter_arrival_time`
- Lean: `Prosa.Analysis.Facts.Periodic.MaxInterArrival.valid_period_is_valid_max_inter_arrival_time`
- Certificate: `valid_period_is_valid_max_inter_arrival_time_correspondence`

## Official Rocq

```coq
valid_period_is_valid_max_inter_arrival_time :
forall {Task : TaskType} {H : PeriodicModel Task} (tsk : Equality.sort Task),
is_true (@valid_period Task H tsk) ->
is_true (@positive_task_max_inter_arrival_time Task (@max_inter_eq_period Task H) tsk)

valid_period_is_valid_max_inter_arrival_time is not universe polymorphic
Arguments valid_period_is_valid_max_inter_arrival_time {Task H} tsk _
valid_period_is_valid_max_inter_arrival_time is opaque
Expands to: Constant
            prosa.analysis.facts.periodic.max_inter_arrival.valid_period_is_valid_max_inter_arrival_time
Declared in library prosa.analysis.facts.periodic.max_inter_arrival, line 28, characters 9-53
@valid_period_is_valid_max_inter_arrival_time
     : forall (Task : TaskType) (H : PeriodicModel Task) (tsk : Equality.sort Task),
       is_true (@valid_period Task H tsk) ->
       is_true (@positive_task_max_inter_arrival_time Task (@max_inter_eq_period Task H) tsk)
```

## Lean

```lean
@Prosa.Analysis.Facts.Periodic.MaxInterArrival.valid_period_is_valid_max_inter_arrival_time : ∀
  {Task : Prosa.Model.Task.Concept.TaskType} [inst : DecidableEq Task]
  [inst_1 : Prosa.Model.Task.Arrival.Periodic.PeriodicModel Task] (tsk : Task),
  Prosa.Model.Task.Arrival.Periodic.valid_period tsk = true →
    Prosa.Model.Task.Arrival.Task_max_inter_arrival.positive_task_max_inter_arrival_time tsk = true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Periodic_MaxInterArrival_valid_period_is_valid_max_inter_arrival_time
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task)
         (inst_6 : 
          Prosa_Model_Task_Arrival_Periodic_PeriodicModel Task
            inst_3)
         (tsk : Task),
       @eq Bool
         (Prosa_Model_Task_Arrival_Periodic_valid_period Task
            inst_3
            inst_6 tsk)
         Bool_true ->
       @eq Bool
         (Prosa_Model_Task_Arrival_Task_max_inter_arrival_positive_task_max_inter_arrival_time Task
            inst_3
            (Prosa_Analysis_Facts_Periodic_MaxInterArrival_max_inter_eq_period Task
               inst_3
               inst_6)
            tsk)
         Bool_true
```
