# `task_cost_positive`

- Kind (Rocq): Definition
- Rocq: `prosa.model.task.concept.task_cost_positive`
- Lean: `Prosa.Model.Task.Concept.task_cost_positive`
- Certificate: ``

## Official Rocq

```coq
task_cost_positive : forall {Task : TaskType}, TaskCost Task -> Equality.sort Task -> bool

task_cost_positive is not universe polymorphic
Arguments task_cost_positive {Task H} tsk
task_cost_positive is transparent
Expands to: Constant prosa.model.task.concept.task_cost_positive
Declared in library prosa.model.task.concept, line 53, characters 15-33
@task_cost_positive
     : forall Task : TaskType, TaskCost Task -> Equality.sort Task -> bool
```

Body:

```coq
task_cost_positive =
fun (Task : TaskType) (H : TaskCost Task) (tsk : Equality.sort Task) => 0 < @task_cost Task H tsk
     : forall {Task : TaskType}, TaskCost Task -> Equality.sort Task -> bool

Arguments task_cost_positive {Task H} tsk
```

## Lean

```lean
@Prosa.Model.Task.Concept.task_cost_positive : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] → [Prosa.Model.Task.Concept.TaskCost Task] → Task → Bool
def Prosa.Model.Task.Concept.task_cost_positive.{u_1} : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] → [Prosa.Model.Task.Concept.TaskCost Task] → Task → Bool :=
fun {Task} [DecidableEq Task] [Prosa.Model.Task.Concept.TaskCost Task] tsk =>
  decide (0 < Prosa.Model.Task.Concept.task_cost tsk)
```

## Lean, imported into Rocq

```coq
Prosa_Model_Task_Concept_task_cost_positive
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Task_Concept_TaskCost Task inst_3 ->
       Task -> Bool
```

Body:

```coq
Prosa_Model_Task_Concept_task_cost_positive@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_3 : DecidableEq Task)
  (inst_6 : Prosa_Model_Task_Concept_TaskCost Task
                                                                     inst_3)
  (tsk : Task) =>
Decidable_decide
  (LT_lt_inst1 Prosa_Behavior_Time_duration instLTNat
     (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 0 (instOfNatNat 0))
     (Prosa_Model_Task_Concept_TaskCost_task_cost Task
        inst_3
        inst_6 tsk))
  (Nat_decLt (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 0 (instOfNatNat 0))
     (Prosa_Model_Task_Concept_TaskCost_task_cost Task
        inst_3
        inst_6 tsk))
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Task_Concept_TaskCost Task inst_3 ->
       Task -> Bool

Arguments Prosa_Model_Task_Concept_task_cost_positive Task
  inst_3
  inst_6 tsk
```
