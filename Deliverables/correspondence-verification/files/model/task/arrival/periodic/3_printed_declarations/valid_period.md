# `valid_period`

- Kind (Rocq): Definition
- Rocq: `prosa.model.task.arrival.periodic.valid_period`
- Lean: `Prosa.Model.Task.Arrival.Periodic.valid_period`
- Certificate: `valid_period_correspondence`

## Official Rocq

```coq
valid_period : forall {Task : TaskType}, PeriodicModel Task -> Equality.sort Task -> bool

valid_period is not universe polymorphic
Arguments valid_period {Task H} tsk
valid_period is transparent
Expands to: Constant prosa.model.task.arrival.periodic.valid_period
Declared in library prosa.model.task.arrival.periodic, line 29, characters 13-25
@valid_period
     : forall Task : TaskType, PeriodicModel Task -> Equality.sort Task -> bool
```

Body:

```coq
valid_period =
fun (Task : TaskType) (H : PeriodicModel Task) (tsk : Equality.sort Task) => 0 < @task_period Task H tsk
     : forall {Task : TaskType}, PeriodicModel Task -> Equality.sort Task -> bool

Arguments valid_period {Task H} tsk
```

## Lean

```lean
@Prosa.Model.Task.Arrival.Periodic.valid_period : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] → [Prosa.Model.Task.Arrival.Periodic.PeriodicModel Task] → Task → Bool
```

Body:

```lean
def Prosa.Model.Task.Arrival.Periodic.valid_period.{u_1} : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] → [Prosa.Model.Task.Arrival.Periodic.PeriodicModel Task] → Task → Bool :=
fun {Task} [DecidableEq Task] [Prosa.Model.Task.Arrival.Periodic.PeriodicModel Task] tsk =>
  decide (0 < Prosa.Model.Task.Arrival.Periodic.task_period tsk)
```

## Lean, imported into Rocq

```coq
Prosa_Model_Task_Arrival_Periodic_valid_period
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Task_Arrival_Periodic_PeriodicModel Task
         inst_3 ->
       Task -> Bool
```

Body:

```coq
Prosa_Model_Task_Arrival_Periodic_valid_period@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_3 : DecidableEq Task)
  (inst_6 : Prosa_Model_Task_Arrival_Periodic_PeriodicModel
                                                                              Task
                                                                              inst_3)
  (tsk : Task) =>
Decidable_decide
  (LT_lt_inst1 Prosa_Behavior_Time_duration instLTNat
     (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 0 (instOfNatNat 0))
     (Prosa_Model_Task_Arrival_Periodic_PeriodicModel_task_period Task
        inst_3
        inst_6 tsk))
  (Nat_decLt (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 0 (instOfNatNat 0))
     (Prosa_Model_Task_Arrival_Periodic_PeriodicModel_task_period Task
        inst_3
        inst_6 tsk))
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Task_Arrival_Periodic_PeriodicModel Task
         inst_3 ->
       Task -> Bool

Arguments Prosa_Model_Task_Arrival_Periodic_valid_period Task
  inst_3
  inst_6 tsk
```
