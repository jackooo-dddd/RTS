# `DM`

- Kind (Rocq): Instance
- Rocq: `prosa.model.priority.deadline_monotonic.DM`
- Lean: `Prosa.Model.Priority.DeadlineMonotonic.DM`
- Certificate: `DM_correspondence`

## Official Rocq

```coq
DM : forall Task : TaskType, TaskDeadline Task -> FP_policy Task

DM is not universe polymorphic
Arguments DM Task {H} _ _
DM is transparent
Expands to: Constant prosa.model.priority.deadline_monotonic.DM
Declared in library prosa.model.priority.deadline_monotonic, line 8, characters 0-159
DM
     : forall Task : TaskType, TaskDeadline Task -> FP_policy Task
```

Body:

```coq
DM =
fun (Task : TaskType) (H : TaskDeadline Task) (tsk1 tsk2 : Equality.sort Task) =>
@task_deadline Task H tsk1 <= @task_deadline Task H tsk2
     : forall Task : TaskType, TaskDeadline Task -> FP_policy Task

Arguments DM Task {H} _ _
```

## Lean

```lean
Prosa.Model.Priority.DeadlineMonotonic.DM : (Task : Prosa.Model.Task.Concept.TaskType) →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Concept.TaskDeadline Task] → Prosa.Model.Priority.Definitions.FP_policy Task
```

Body:

```lean
@[instance_reducible] def Prosa.Model.Priority.DeadlineMonotonic.DM.{u_1} : (Task : Prosa.Model.Task.Concept.TaskType) →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Concept.TaskDeadline Task] → Prosa.Model.Priority.Definitions.FP_policy Task :=
fun Task [DecidableEq Task] [Prosa.Model.Task.Concept.TaskDeadline Task] =>
  {
    hep_task := fun tsk1 tsk2 =>
      decide (Prosa.Model.Task.Concept.task_deadline tsk1 ≤ Prosa.Model.Task.Concept.task_deadline tsk2) }
```

## Lean, imported into Rocq

```coq
Prosa_Model_Priority_DeadlineMonotonic_DM
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Task_Concept_TaskDeadline Task
         inst_3 ->
       Prosa_Model_Priority_Definitions_FP_policy Task
         inst_3
```

Body:

```coq
Prosa_Model_Priority_DeadlineMonotonic_DM@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_3 : DecidableEq Task)
  (inst_6 : Prosa_Model_Task_Concept_TaskDeadline
                                                                                Task
                                                                                inst_3) =>
Prosa_Model_Priority_Definitions_FP_policy_mk Task
  inst_3
  (fun tsk1 tsk2 : Task =>
   Decidable_decide
     (LE_le_inst1 Prosa_Behavior_Time_duration instLENat
        (Prosa_Model_Task_Concept_TaskDeadline_task_deadline Task
           inst_3
           inst_6 tsk1)
        (Prosa_Model_Task_Concept_TaskDeadline_task_deadline Task
           inst_3
           inst_6 tsk2))
     (Nat_decLe
        (Prosa_Model_Task_Concept_TaskDeadline_task_deadline Task
           inst_3
           inst_6 tsk1)
        (Prosa_Model_Task_Concept_TaskDeadline_task_deadline Task
           inst_3
           inst_6 tsk2)))
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Task_Concept_TaskDeadline Task
         inst_3 ->
       Prosa_Model_Priority_Definitions_FP_policy Task
         inst_3

Arguments Prosa_Model_Priority_DeadlineMonotonic_DM Task
  inst_3
  inst_6
```
