# `fully_nonpreemptive_task_model`

- Kind (Rocq): Definition
- Rocq: `prosa.model.task.preemption.fully_nonpreemptive.fully_nonpreemptive_task_model`
- Lean: `Prosa.Model.Task.Preemption.FullyNonpreemptive.fully_nonpreemptive_task_model`
- Certificate: `fully_nonpreemptive_task_model_correspondence`

## Official Rocq

```coq
fully_nonpreemptive_task_model : forall {Task : TaskType}, TaskCost Task -> TaskMaxNonpreemptiveSegment Task

fully_nonpreemptive_task_model is not universe polymorphic
Arguments fully_nonpreemptive_task_model {Task H} _
fully_nonpreemptive_task_model is transparent
Expands to: Constant prosa.model.task.preemption.fully_nonpreemptive.fully_nonpreemptive_task_model
Declared in library prosa.model.task.preemption.fully_nonpreemptive, line 16, characters 13-43
@fully_nonpreemptive_task_model
     : forall Task : TaskType, TaskCost Task -> TaskMaxNonpreemptiveSegment Task
```

Body:

```coq
fully_nonpreemptive_task_model =
fun (Task : TaskType) (H : TaskCost Task) => [eta @task_cost Task H]
     : forall {Task : TaskType}, TaskCost Task -> TaskMaxNonpreemptiveSegment Task

Arguments fully_nonpreemptive_task_model {Task H} _
```

## Lean

```lean
@Prosa.Model.Task.Preemption.FullyNonpreemptive.fully_nonpreemptive_task_model : {Task :
    Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Concept.TaskCost Task] → Prosa.Model.Task.Preemption.Parameters.TaskMaxNonpreemptiveSegment Task
```

Body:

```lean
@[reducible] def Prosa.Model.Task.Preemption.FullyNonpreemptive.fully_nonpreemptive_task_model.{u_1} : {Task :
    Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Concept.TaskCost Task] →
      Prosa.Model.Task.Preemption.Parameters.TaskMaxNonpreemptiveSegment Task :=
fun {Task} [DecidableEq Task] [Prosa.Model.Task.Concept.TaskCost Task] =>
  { task_max_nonpreemptive_segment := fun tsk => Prosa.Model.Task.Concept.task_cost tsk }
```

## Lean, imported into Rocq

```coq
Prosa_Model_Task_Preemption_FullyNonpreemptive_fully_nonpreemptive_task_model
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task),
       Prosa_Model_Task_Concept_TaskCost Task
         inst_3 ->
       Prosa_Model_Task_Preemption_Parameters_TaskMaxNonpreemptiveSegment Task
         inst_3
```

Body:

```coq
Prosa_Model_Task_Preemption_FullyNonpreemptive_fully_nonpreemptive_task_model@{u_1 Lean.u_1+1.0
Lean.u_1+2.0} =
fun (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_3 : DecidableEq Task)
  (inst_6 : 
   Prosa_Model_Task_Concept_TaskCost Task
     inst_3) =>
Prosa_Model_Task_Preemption_Parameters_TaskMaxNonpreemptiveSegment_mk Task
  inst_3
  (fun tsk : Task =>
   Prosa_Model_Task_Concept_TaskCost_task_cost Task
     inst_3
     inst_6 tsk)
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task),
       Prosa_Model_Task_Concept_TaskCost Task
         inst_3 ->
       Prosa_Model_Task_Preemption_Parameters_TaskMaxNonpreemptiveSegment Task
         inst_3

Arguments Prosa_Model_Task_Preemption_FullyNonpreemptive_fully_nonpreemptive_task_model 
  Task inst_3
  inst_6
```
