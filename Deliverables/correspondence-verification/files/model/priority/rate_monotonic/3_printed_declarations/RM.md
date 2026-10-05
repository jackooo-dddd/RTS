# `RM`

- Kind (Rocq): Instance
- Rocq: `prosa.model.priority.rate_monotonic.RM`
- Lean: `Prosa.Model.Priority.RateMonotonic.RM`
- Certificate: `RM_correspondence`

## Official Rocq

```coq
RM : forall Task : TaskType, SporadicModel Task -> FP_policy Task

RM is not universe polymorphic
Arguments RM Task {H} _ _
RM is transparent
Expands to: Constant prosa.model.priority.rate_monotonic.RM
Declared in library prosa.model.priority.rate_monotonic, line 10, characters 0-188
RM
     : forall Task : TaskType, SporadicModel Task -> FP_policy Task
```

Body:

```coq
RM =
fun (Task : TaskType) (H : SporadicModel Task) (tsk1 tsk2 : Equality.sort Task) =>
@task_min_inter_arrival_time Task H tsk1 <= @task_min_inter_arrival_time Task H tsk2
     : forall Task : TaskType, SporadicModel Task -> FP_policy Task

Arguments RM Task {H} _ _
```

## Lean

```lean
Prosa.Model.Priority.RateMonotonic.RM : (Task : Prosa.Model.Task.Concept.TaskType) →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Arrival.Sporadic.SporadicModel Task] → Prosa.Model.Priority.Definitions.FP_policy Task
```

Body:

```lean
@[instance_reducible] def Prosa.Model.Priority.RateMonotonic.RM.{u_1} : (Task : Prosa.Model.Task.Concept.TaskType) →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Arrival.Sporadic.SporadicModel Task] → Prosa.Model.Priority.Definitions.FP_policy Task :=
fun Task [DecidableEq Task] [Prosa.Model.Task.Arrival.Sporadic.SporadicModel Task] =>
  {
    hep_task := fun tsk1 tsk2 =>
      decide
        (Prosa.Model.Task.Arrival.Sporadic.task_min_inter_arrival_time tsk1 ≤
          Prosa.Model.Task.Arrival.Sporadic.task_min_inter_arrival_time tsk2) }
```

## Lean, imported into Rocq

```coq
Prosa_Model_Priority_RateMonotonic_RM
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Task_Arrival_Sporadic_SporadicModel Task
         inst_3 ->
       Prosa_Model_Priority_Definitions_FP_policy Task
         inst_3
```

Body:

```coq
Prosa_Model_Priority_RateMonotonic_RM@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_3 : DecidableEq Task)
  (inst_6 : Prosa_Model_Task_Arrival_Sporadic_SporadicModel
                                                                              Task
                                                                              inst_3) =>
Prosa_Model_Priority_Definitions_FP_policy_mk Task
  inst_3
  (fun tsk1 tsk2 : Task =>
   Decidable_decide
     (LE_le_inst1 Prosa_Behavior_Time_duration instLENat
        (Prosa_Model_Task_Arrival_Sporadic_SporadicModel_task_min_inter_arrival_time Task
           inst_3
           inst_6 tsk1)
        (Prosa_Model_Task_Arrival_Sporadic_SporadicModel_task_min_inter_arrival_time Task
           inst_3
           inst_6 tsk2))
     (Nat_decLe
        (Prosa_Model_Task_Arrival_Sporadic_SporadicModel_task_min_inter_arrival_time Task
           inst_3
           inst_6 tsk1)
        (Prosa_Model_Task_Arrival_Sporadic_SporadicModel_task_min_inter_arrival_time Task
           inst_3
           inst_6 tsk2)))
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Task_Arrival_Sporadic_SporadicModel Task
         inst_3 ->
       Prosa_Model_Priority_Definitions_FP_policy Task
         inst_3

Arguments Prosa_Model_Priority_RateMonotonic_RM Task
  inst_3
  inst_6
```
