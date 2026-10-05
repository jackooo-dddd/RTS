# `task_rtc_bounded_by_cost`

- Kind (Rocq): Definition
- Rocq: `prosa.model.task.preemption.parameters.task_rtc_bounded_by_cost`
- Lean: `Prosa.Model.Task.Preemption.Parameters.task_rtc_bounded_by_cost`
- Certificate: `task_rtc_bounded_by_cost_correspondence`

## Official Rocq

```coq
task_rtc_bounded_by_cost :
forall {Task : TaskType}, TaskCost Task -> TaskRunToCompletionThreshold Task -> Equality.sort Task -> bool

task_rtc_bounded_by_cost is not universe polymorphic
Arguments task_rtc_bounded_by_cost {Task H H3} tsk
task_rtc_bounded_by_cost is transparent
Expands to: Constant prosa.model.task.preemption.parameters.task_rtc_bounded_by_cost
Declared in library prosa.model.task.preemption.parameters, line 163, characters 13-37
@task_rtc_bounded_by_cost
     : forall Task : TaskType,
       TaskCost Task -> TaskRunToCompletionThreshold Task -> Equality.sort Task -> bool
```

Body:

```coq
task_rtc_bounded_by_cost =
fun (Task : TaskType) (H : TaskCost Task) (H3 : TaskRunToCompletionThreshold Task) (tsk : Equality.sort Task) =>
@task_rtct Task H3 tsk <= @task_cost Task H tsk
     : forall {Task : TaskType},
       TaskCost Task -> TaskRunToCompletionThreshold Task -> Equality.sort Task -> bool

Arguments task_rtc_bounded_by_cost {Task H H3} tsk
```

## Lean

```lean
@Prosa.Model.Task.Preemption.Parameters.task_rtc_bounded_by_cost : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Concept.TaskCost Task] →
      [Prosa.Model.Task.Preemption.Parameters.TaskRunToCompletionThreshold Task] → Task → Bool
```

Body:

```lean
def Prosa.Model.Task.Preemption.Parameters.task_rtc_bounded_by_cost.{u_1} : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Concept.TaskCost Task] →
      [Prosa.Model.Task.Preemption.Parameters.TaskRunToCompletionThreshold Task] → Task → Bool :=
fun {Task} [DecidableEq Task] [Prosa.Model.Task.Concept.TaskCost Task]
    [Prosa.Model.Task.Preemption.Parameters.TaskRunToCompletionThreshold Task] tsk =>
  decide (Prosa.Model.Task.Preemption.Parameters.task_rtct tsk ≤ Prosa.Model.Task.Concept.task_cost tsk)
```

## Lean, imported into Rocq

```coq
Prosa_Model_Task_Preemption_Parameters_task_rtc_bounded_by_cost
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Task_Concept_TaskCost Task
         inst_3 ->
       Prosa_Model_Task_Preemption_Parameters_TaskRunToCompletionThreshold Task
         inst_3 ->
       Task -> Bool
```

Body:

```coq
Prosa_Model_Task_Preemption_Parameters_task_rtc_bounded_by_cost@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_3 : DecidableEq Task)
  (inst_6 : 
   Prosa_Model_Task_Concept_TaskCost Task
     inst_3)
  (inst_9 : 
   Prosa_Model_Task_Preemption_Parameters_TaskRunToCompletionThreshold Task
     inst_3)
  (tsk : Task) =>
Decidable_decide
  (LE_le_inst1 Prosa_Behavior_Job_work instLENat
     (Prosa_Model_Task_Preemption_Parameters_TaskRunToCompletionThreshold_task_rtct Task
        inst_3
        inst_9 tsk)
     (Prosa_Model_Task_Concept_TaskCost_task_cost Task
        inst_3
        inst_6 tsk))
  (Nat_decLe
     (Prosa_Model_Task_Preemption_Parameters_TaskRunToCompletionThreshold_task_rtct Task
        inst_3
        inst_9 tsk)
     (Prosa_Model_Task_Concept_TaskCost_task_cost Task
        inst_3
        inst_6 tsk))
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Task_Concept_TaskCost Task
         inst_3 ->
       Prosa_Model_Task_Preemption_Parameters_TaskRunToCompletionThreshold Task
         inst_3 ->
       Task -> Bool

Arguments Prosa_Model_Task_Preemption_Parameters_task_rtc_bounded_by_cost Task
  inst_3
  inst_6
  inst_9 j
```
