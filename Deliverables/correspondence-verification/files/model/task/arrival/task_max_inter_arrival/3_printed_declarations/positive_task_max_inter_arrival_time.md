# `positive_task_max_inter_arrival_time`

- Kind (Rocq): Definition
- Rocq: `prosa.model.task.arrival.task_max_inter_arrival.positive_task_max_inter_arrival_time`
- Lean: `Prosa.Model.Task.Arrival.Task_max_inter_arrival.positive_task_max_inter_arrival_time`
- Certificate: `positive_task_max_inter_arrival_time_correspondence`

## Official Rocq

```coq
positive_task_max_inter_arrival_time :
forall {Task : TaskType}, TaskMaxInterArrival Task -> Equality.sort Task -> bool

positive_task_max_inter_arrival_time is not universe polymorphic
Arguments positive_task_max_inter_arrival_time {Task H} tsk
positive_task_max_inter_arrival_time is transparent
Expands to: Constant prosa.model.task.arrival.task_max_inter_arrival.positive_task_max_inter_arrival_time
Declared in library prosa.model.task.arrival.task_max_inter_arrival, line 28, characters 13-49
@positive_task_max_inter_arrival_time
     : forall Task : TaskType, TaskMaxInterArrival Task -> Equality.sort Task -> bool
```

Body:

```coq
positive_task_max_inter_arrival_time =
fun (Task : TaskType) (H : TaskMaxInterArrival Task) (tsk : Equality.sort Task) =>
0 < @task_max_inter_arrival_time Task H tsk
     : forall {Task : TaskType}, TaskMaxInterArrival Task -> Equality.sort Task -> bool

Arguments positive_task_max_inter_arrival_time {Task H} tsk
```

## Lean

```lean
@Prosa.Model.Task.Arrival.Task_max_inter_arrival.positive_task_max_inter_arrival_time : {Task :
    Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] → [Prosa.Model.Task.Arrival.Task_max_inter_arrival.TaskMaxInterArrival Task] → Task → Bool
def Prosa.Model.Task.Arrival.Task_max_inter_arrival.positive_task_max_inter_arrival_time.{u_1} : {Task :
    Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Arrival.Task_max_inter_arrival.TaskMaxInterArrival Task] → Task → Bool :=
fun {Task} [DecidableEq Task] [Prosa.Model.Task.Arrival.Task_max_inter_arrival.TaskMaxInterArrival Task] tsk =>
  decide (0 < Prosa.Model.Task.Arrival.Task_max_inter_arrival.task_max_inter_arrival_time tsk)
```

## Lean, imported into Rocq

```coq
Prosa_Model_Task_Arrival_Task_max_inter_arrival_positive_task_max_inter_arrival_time
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task),
       Prosa_Model_Task_Arrival_Task_max_inter_arrival_TaskMaxInterArrival Task
         inst_3 ->
       Task -> Bool
```

Body:

```coq
Prosa_Model_Task_Arrival_Task_max_inter_arrival_positive_task_max_inter_arrival_time@{u_1 Lean.u_1+1.0
Lean.u_1+2.0} =
fun (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_3 : DecidableEq Task)
  (inst_6 : 
   Prosa_Model_Task_Arrival_Task_max_inter_arrival_TaskMaxInterArrival Task
     inst_3)
  (tsk : Task) =>
Decidable_decide
  (LT_lt_inst1 Prosa_Behavior_Time_duration instLTNat
     (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 0 (instOfNatNat 0))
     (Prosa_Model_Task_Arrival_Task_max_inter_arrival_TaskMaxInterArrival_task_max_inter_arrival_time Task
        inst_3
        inst_6 tsk))
  (Nat_decLt (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 0 (instOfNatNat 0))
     (Prosa_Model_Task_Arrival_Task_max_inter_arrival_TaskMaxInterArrival_task_max_inter_arrival_time Task
        inst_3
        inst_6 tsk))
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task),
       Prosa_Model_Task_Arrival_Task_max_inter_arrival_TaskMaxInterArrival Task
         inst_3 ->
       Task -> Bool

Arguments Prosa_Model_Task_Arrival_Task_max_inter_arrival_positive_task_max_inter_arrival_time 
  Task inst_3
  inst_6 
  tsk
```
