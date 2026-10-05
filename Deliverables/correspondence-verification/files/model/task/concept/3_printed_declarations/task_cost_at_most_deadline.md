# `task_cost_at_most_deadline`

- Kind (Rocq): Definition
- Rocq: `prosa.model.task.concept.task_cost_at_most_deadline`
- Lean: `Prosa.Model.Task.Concept.task_cost_at_most_deadline`
- Certificate: ``

## Official Rocq

```coq
task_cost_at_most_deadline :
forall {Task : TaskType}, TaskCost Task -> TaskDeadline Task -> Equality.sort Task -> bool

task_cost_at_most_deadline is not universe polymorphic
Arguments task_cost_at_most_deadline {Task H H1} tsk
task_cost_at_most_deadline is transparent
Expands to: Constant prosa.model.task.concept.task_cost_at_most_deadline
Declared in library prosa.model.task.concept, line 57, characters 15-41
@task_cost_at_most_deadline
     : forall Task : TaskType, TaskCost Task -> TaskDeadline Task -> Equality.sort Task -> bool
```

Body:

```coq
task_cost_at_most_deadline =
fun (Task : TaskType) (H : TaskCost Task) (H1 : TaskDeadline Task) (tsk : Equality.sort Task) =>
@task_cost Task H tsk <= @task_deadline Task H1 tsk
     : forall {Task : TaskType}, TaskCost Task -> TaskDeadline Task -> Equality.sort Task -> bool

Arguments task_cost_at_most_deadline {Task H H1} tsk
```

## Lean

```lean
@Prosa.Model.Task.Concept.task_cost_at_most_deadline : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Concept.TaskCost Task] → [Prosa.Model.Task.Concept.TaskDeadline Task] → Task → Bool
def Prosa.Model.Task.Concept.task_cost_at_most_deadline.{u_1} : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Concept.TaskCost Task] → [Prosa.Model.Task.Concept.TaskDeadline Task] → Task → Bool :=
fun {Task} [DecidableEq Task] [Prosa.Model.Task.Concept.TaskCost Task] [Prosa.Model.Task.Concept.TaskDeadline Task]
    tsk =>
  decide (Prosa.Model.Task.Concept.task_cost tsk ≤ Prosa.Model.Task.Concept.task_deadline tsk)
```

## Lean, imported into Rocq

```coq
Prosa_Model_Task_Concept_task_cost_at_most_deadline
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Task_Concept_TaskCost Task inst_3 ->
       Prosa_Model_Task_Concept_TaskDeadline Task
         inst_3 ->
       Task -> Bool
```

Body:

```coq
Prosa_Model_Task_Concept_task_cost_at_most_deadline@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_3 : DecidableEq Task)
  (inst_6 : Prosa_Model_Task_Concept_TaskCost Task
                                                                    inst_3)
  (inst_12 : Prosa_Model_Task_Concept_TaskDeadline Task
                                                                     inst_3)
  (tsk : Task) =>
Decidable_decide
  (LE_le_inst1 Prosa_Behavior_Time_duration instLENat
     (Prosa_Model_Task_Concept_TaskCost_task_cost Task
        inst_3
        inst_6 tsk)
     (Prosa_Model_Task_Concept_TaskDeadline_task_deadline Task
        inst_3
        inst_12 tsk))
  (Nat_decLe
     (Prosa_Model_Task_Concept_TaskCost_task_cost Task
        inst_3
        inst_6 tsk)
     (Prosa_Model_Task_Concept_TaskDeadline_task_deadline Task
        inst_3
        inst_12 tsk))
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Task_Concept_TaskCost Task inst_3 ->
       Prosa_Model_Task_Concept_TaskDeadline Task
         inst_3 ->
       Task -> Bool

Arguments Prosa_Model_Task_Concept_task_cost_at_most_deadline Task
  inst_3
  inst_6
  inst_12 tsk
```
