# `task_end_of_execution_in_preemption_points`

- Kind (Rocq): Definition
- Rocq: `prosa.model.task.preemption.limited_preemptive.task_end_of_execution_in_preemption_points`
- Lean: `Prosa.Model.Task.Preemption.LimitedPreemptive.task_end_of_execution_in_preemption_points`
- Certificate: `task_end_of_execution_in_preemption_points_correspondence`

## Official Rocq

```coq
task_end_of_execution_in_preemption_points :
forall {Task : TaskType}, TaskCost Task -> TaskPreemptionPoints Task -> TaskSet (Equality.sort Task) -> Prop

task_end_of_execution_in_preemption_points is not universe polymorphic
Arguments task_end_of_execution_in_preemption_points {Task H H0} ts
task_end_of_execution_in_preemption_points is transparent
Expands to: Constant
            prosa.model.task.preemption.limited_preemptive.task_end_of_execution_in_preemption_points
Declared in library prosa.model.task.preemption.limited_preemptive, line 44, characters 13-55
@task_end_of_execution_in_preemption_points
     : forall Task : TaskType,
       TaskCost Task -> TaskPreemptionPoints Task -> TaskSet (Equality.sort Task) -> Prop
```

Body:

```coq
task_end_of_execution_in_preemption_points =
fun (Task : TaskType) (H : TaskCost Task) (H0 : TaskPreemptionPoints Task)
  (ts : TaskSet (Equality.sort Task)) =>
forall tsk : Equality.sort Task,
is_true (tsk \in ts) -> last0 (@task_preemption_points Task H0 tsk) = @task_cost Task H tsk
     : forall {Task : TaskType},
       TaskCost Task -> TaskPreemptionPoints Task -> TaskSet (Equality.sort Task) -> Prop

Arguments task_end_of_execution_in_preemption_points {Task H H0} ts
```

## Lean

```lean
@Prosa.Model.Task.Preemption.LimitedPreemptive.task_end_of_execution_in_preemption_points : {Task :
    Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Concept.TaskCost Task] →
      [Prosa.Model.Task.Preemption.Parameters.TaskPreemptionPoints Task] → Prosa.Model.Task.Concept.TaskSet Task → Prop
```

Body:

```lean
def Prosa.Model.Task.Preemption.LimitedPreemptive.task_end_of_execution_in_preemption_points.{u_1} : {Task :
    Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Concept.TaskCost Task] →
      [Prosa.Model.Task.Preemption.Parameters.TaskPreemptionPoints Task] →
        Prosa.Model.Task.Concept.TaskSet Task → Prop :=
fun {Task} [DecidableEq Task] [Prosa.Model.Task.Concept.TaskCost Task]
    [Prosa.Model.Task.Preemption.Parameters.TaskPreemptionPoints Task] ts =>
  ∀ (tsk : Task),
    decide (tsk ∈ ts) = true →
      Prosa.Util.List.last0 (Prosa.Model.Task.Preemption.Parameters.task_preemption_points tsk) =
        Prosa.Model.Task.Concept.task_cost tsk
```

## Lean, imported into Rocq

```coq
Prosa_Model_Task_Preemption_LimitedPreemptive_task_end_of_execution_in_preemption_points
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task),
       Prosa_Model_Task_Concept_TaskCost Task
         inst_3 ->
       Prosa_Model_Task_Preemption_Parameters_TaskPreemptionPoints Task
         inst_3 ->
       Prosa_Model_Task_Concept_TaskSet Task -> SProp
```

Body:

```coq
Prosa_Model_Task_Preemption_LimitedPreemptive_task_end_of_execution_in_preemption_points@{u_1 Lean.u_1+1.0
Lean.u_1+2.0} =
fun (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_3 : DecidableEq Task)
  (inst_6 : 
   Prosa_Model_Task_Concept_TaskCost Task
     inst_3)
  (inst_9 : 
   Prosa_Model_Task_Preemption_Parameters_TaskPreemptionPoints Task
     inst_3)
  (ts : Prosa_Model_Task_Concept_TaskSet Task) =>
forall tsk : Task,
@eq Bool
  (Decidable_decide
     (Membership_mem Task (Prosa_Model_Task_Concept_TaskSet Task) (List_instMembership Task) ts tsk)
     (List_instDecidableMemOfLawfulBEq Task
        (instBEqOfDecidableEq Task
           inst_3)
        (instLawfulBEq Task
           inst_3)
        tsk ts))
  Bool_true ->
@eq Nat
  (Prosa_Util_List_last0
     (Prosa_Model_Task_Preemption_Parameters_TaskPreemptionPoints_task_preemption_points Task
        inst_3
        inst_9 tsk))
  (Prosa_Model_Task_Concept_TaskCost_task_cost Task
     inst_3
     inst_6 tsk)
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task),
       Prosa_Model_Task_Concept_TaskCost Task
         inst_3 ->
       Prosa_Model_Task_Preemption_Parameters_TaskPreemptionPoints Task
         inst_3 ->
       Prosa_Model_Task_Concept_TaskSet Task -> SProp

Arguments Prosa_Model_Task_Preemption_LimitedPreemptive_task_end_of_execution_in_preemption_points 
  Task inst_3
  inst_6
  inst_9 
  ts
```
