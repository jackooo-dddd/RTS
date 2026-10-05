# `fully_preemptive_task_model`

- Kind (Rocq): Definition
- Rocq: `prosa.model.task.preemption.fully_preemptive.fully_preemptive_task_model`
- Lean: `Prosa.Model.Task.Preemption.FullyPreemptive.fully_preemptive_task_model`
- Certificate: `fully_preemptive_task_model_correspondence`

## Official Rocq

```coq
fully_preemptive_task_model : forall {Task : TaskType}, TaskMaxNonpreemptiveSegment Task

fully_preemptive_task_model is not universe polymorphic
Arguments fully_preemptive_task_model {Task} _
fully_preemptive_task_model is transparent
Expands to: Constant prosa.model.task.preemption.fully_preemptive.fully_preemptive_task_model
Declared in library prosa.model.task.preemption.fully_preemptive, line 16, characters 13-40
@fully_preemptive_task_model
     : forall Task : TaskType, TaskMaxNonpreemptiveSegment Task
```

Body:

```coq
fully_preemptive_task_model =
fun Task : TaskType => fun=> 1
     : forall {Task : TaskType}, TaskMaxNonpreemptiveSegment Task

Arguments fully_preemptive_task_model {Task} _
```

## Lean

```lean
@Prosa.Model.Task.Preemption.FullyPreemptive.fully_preemptive_task_model : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] → Prosa.Model.Task.Preemption.Parameters.TaskMaxNonpreemptiveSegment Task
```

Body:

```lean
@[reducible] def Prosa.Model.Task.Preemption.FullyPreemptive.fully_preemptive_task_model.{u_1} : {Task :
    Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] → Prosa.Model.Task.Preemption.Parameters.TaskMaxNonpreemptiveSegment Task :=
fun {Task} [DecidableEq Task] => { task_max_nonpreemptive_segment := fun x => 1 }
```

## Lean, imported into Rocq

```coq
Prosa_Model_Task_Preemption_FullyPreemptive_fully_preemptive_task_model
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task),
       Prosa_Model_Task_Preemption_Parameters_TaskMaxNonpreemptiveSegment Task
         inst_3
```

Body:

```coq
Prosa_Model_Task_Preemption_FullyPreemptive_fully_preemptive_task_model@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_3 : DecidableEq Task) =>
Prosa_Model_Task_Preemption_Parameters_TaskMaxNonpreemptiveSegment_mk Task
  inst_3
  (fun _ : Task => OfNat_ofNat_inst1 Prosa_Behavior_Job_work 1 (instOfNatNat 1))
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task),
       Prosa_Model_Task_Preemption_Parameters_TaskMaxNonpreemptiveSegment Task
         inst_3

Arguments Prosa_Model_Task_Preemption_FullyPreemptive_fully_preemptive_task_model 
  Task inst_3
```
