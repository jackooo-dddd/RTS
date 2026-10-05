# `task_last_nonpr_segment`

- Kind (Rocq): Definition
- Rocq: `prosa.model.task.preemption.parameters.task_last_nonpr_segment`
- Lean: `Prosa.Model.Task.Preemption.Parameters.task_last_nonpr_segment`
- Certificate: `task_last_nonpr_segment_correspondence`

## Official Rocq

```coq
task_last_nonpr_segment : forall {Task : TaskType}, TaskPreemptionPoints Task -> Equality.sort Task -> nat

task_last_nonpr_segment is not universe polymorphic
Arguments task_last_nonpr_segment {Task H} tsk
task_last_nonpr_segment is transparent
Expands to: Constant prosa.model.task.preemption.parameters.task_last_nonpr_segment
Declared in library prosa.model.task.preemption.parameters, line 47, characters 13-36
@task_last_nonpr_segment
     : forall Task : TaskType, TaskPreemptionPoints Task -> Equality.sort Task -> nat
```

Body:

```coq
task_last_nonpr_segment =
fun (Task : TaskType) (H : TaskPreemptionPoints Task) (tsk : Equality.sort Task) =>
last0 (distances (@task_preemption_points Task H tsk))
     : forall {Task : TaskType}, TaskPreemptionPoints Task -> Equality.sort Task -> nat

Arguments task_last_nonpr_segment {Task H} tsk
```

## Lean

```lean
@Prosa.Model.Task.Preemption.Parameters.task_last_nonpr_segment : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] → [Prosa.Model.Task.Preemption.Parameters.TaskPreemptionPoints Task] → Task → ℕ
```

Body:

```lean
def Prosa.Model.Task.Preemption.Parameters.task_last_nonpr_segment.{u_1} : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] → [Prosa.Model.Task.Preemption.Parameters.TaskPreemptionPoints Task] → Task → ℕ :=
fun {Task} [DecidableEq Task] [Prosa.Model.Task.Preemption.Parameters.TaskPreemptionPoints Task] tsk =>
  Prosa.Util.List.last0
    (Prosa.Util.Nondecreasing.distances (Prosa.Model.Task.Preemption.Parameters.task_preemption_points tsk))
```

## Lean, imported into Rocq

```coq
Prosa_Model_Task_Preemption_Parameters_task_last_nonpr_segment
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Task_Preemption_Parameters_TaskPreemptionPoints Task
         inst_3 ->
       Task -> Nat
```

Body:

```coq
Prosa_Model_Task_Preemption_Parameters_task_last_nonpr_segment@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_3 : DecidableEq Task)
  (inst_6 : Prosa_Model_Task_Preemption_Parameters_TaskPreemptionPoints
                                                                                Task
                                                                                inst_3)
  (tsk : Task) =>
Prosa_Util_List_last0
  (Prosa_Util_Nondecreasing_distances
     (Prosa_Model_Task_Preemption_Parameters_TaskPreemptionPoints_task_preemption_points Task
        inst_3
        inst_6 tsk))
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Task_Preemption_Parameters_TaskPreemptionPoints Task
         inst_3 ->
       Task -> Nat

Arguments Prosa_Model_Task_Preemption_Parameters_task_last_nonpr_segment Task
  inst_3
  inst_6 tsk
```
