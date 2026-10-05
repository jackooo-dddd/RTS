# `TaskPreemptionPoints_to_TaskMaxNonpreemptiveSegment_conversion`

- Kind (Rocq): Instance
- Rocq: `prosa.model.task.preemption.parameters.TaskPreemptionPoints_to_TaskMaxNonpreemptiveSegment_conversion`
- Lean: `Prosa.Model.Task.Preemption.Parameters.TaskPreemptionPoints_to_TaskMaxNonpreemptiveSegment_conversion`
- Certificate: `TaskPreemptionPoints_to_TaskMaxNonpreemptiveSegment_conversion_correspondence`

## Official Rocq

```coq
TaskPreemptionPoints_to_TaskMaxNonpreemptiveSegment_conversion :
forall Task : TaskType, TaskPreemptionPoints Task -> TaskMaxNonpreemptiveSegment Task

TaskPreemptionPoints_to_TaskMaxNonpreemptiveSegment_conversion is not universe polymorphic
Arguments TaskPreemptionPoints_to_TaskMaxNonpreemptiveSegment_conversion Task {H} _
TaskPreemptionPoints_to_TaskMaxNonpreemptiveSegment_conversion is transparent
Expands to: Constant
            prosa.model.task.preemption.parameters.TaskPreemptionPoints_to_TaskMaxNonpreemptiveSegment_conversion
Declared in library prosa.model.task.preemption.parameters, line 55, characters 0-199
TaskPreemptionPoints_to_TaskMaxNonpreemptiveSegment_conversion
     : forall Task : TaskType, TaskPreemptionPoints Task -> TaskMaxNonpreemptiveSegment Task
```

Body:

```coq
TaskPreemptionPoints_to_TaskMaxNonpreemptiveSegment_conversion =
fun Task : TaskType => [eta @task_max_nonpr_segment Task]
     : forall Task : TaskType, TaskPreemptionPoints Task -> TaskMaxNonpreemptiveSegment Task

Arguments TaskPreemptionPoints_to_TaskMaxNonpreemptiveSegment_conversion Task {H} _
```

## Lean

```lean
Prosa.Model.Task.Preemption.Parameters.TaskPreemptionPoints_to_TaskMaxNonpreemptiveSegment_conversion : (Task :
    Prosa.Model.Task.Concept.TaskType) →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Preemption.Parameters.TaskPreemptionPoints Task] →
      Prosa.Model.Task.Preemption.Parameters.TaskMaxNonpreemptiveSegment Task
```

Body:

```lean
@[instance_reducible] def Prosa.Model.Task.Preemption.Parameters.TaskPreemptionPoints_to_TaskMaxNonpreemptiveSegment_conversion.{u_1} : (Task :
    Prosa.Model.Task.Concept.TaskType) →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Preemption.Parameters.TaskPreemptionPoints Task] →
      Prosa.Model.Task.Preemption.Parameters.TaskMaxNonpreemptiveSegment Task :=
fun Task [DecidableEq Task] [Prosa.Model.Task.Preemption.Parameters.TaskPreemptionPoints Task] =>
  { task_max_nonpreemptive_segment := Prosa.Model.Task.Preemption.Parameters.task_max_nonpr_segment }
```

## Lean, imported into Rocq

```coq
Prosa_Model_Task_Preemption_Parameters_TaskPreemptionPoints_to_TaskMaxNonpreemptiveSegment_conversion
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Task_Preemption_Parameters_TaskPreemptionPoints Task
         inst_3 ->
       Prosa_Model_Task_Preemption_Parameters_TaskMaxNonpreemptiveSegment Task
         inst_3
```

Body:

```coq
Prosa_Model_Task_Preemption_Parameters_TaskPreemptionPoints_to_TaskMaxNonpreemptiveSegment_conversion@{u_1
Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_3 : DecidableEq Task)
  (inst_6 : 
   Prosa_Model_Task_Preemption_Parameters_TaskPreemptionPoints Task
     inst_3) =>
Prosa_Model_Task_Preemption_Parameters_TaskMaxNonpreemptiveSegment_mk Task
  inst_3
  (Prosa_Model_Task_Preemption_Parameters_task_max_nonpr_segment Task
     inst_3
     inst_6)
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Task_Preemption_Parameters_TaskPreemptionPoints Task
         inst_3 ->
       Prosa_Model_Task_Preemption_Parameters_TaskMaxNonpreemptiveSegment Task
         inst_3

Arguments
  Prosa_Model_Task_Preemption_Parameters_TaskPreemptionPoints_to_TaskMaxNonpreemptiveSegment_conversion 
  Task inst_3
  inst_6
```
