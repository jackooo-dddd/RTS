# `nondecreasing_task_preemption_points`

- Kind (Rocq): Definition
- Rocq: `prosa.model.task.preemption.limited_preemptive.nondecreasing_task_preemption_points`
- Lean: `Prosa.Model.Task.Preemption.LimitedPreemptive.nondecreasing_task_preemption_points`
- Certificate: `nondecreasing_task_preemption_points_correspondence`

## Official Rocq

```coq
nondecreasing_task_preemption_points :
forall {Task : TaskType}, TaskPreemptionPoints Task -> TaskSet (Equality.sort Task) -> Prop

nondecreasing_task_preemption_points is not universe polymorphic
Arguments nondecreasing_task_preemption_points {Task H0} ts
nondecreasing_task_preemption_points is transparent
Expands to: Constant prosa.model.task.preemption.limited_preemptive.nondecreasing_task_preemption_points
Declared in library prosa.model.task.preemption.limited_preemptive, line 49, characters 13-49
@nondecreasing_task_preemption_points
     : forall Task : TaskType, TaskPreemptionPoints Task -> TaskSet (Equality.sort Task) -> Prop
```

Body:

```coq
nondecreasing_task_preemption_points =
fun (Task : TaskType) (H0 : TaskPreemptionPoints Task) (ts : TaskSet (Equality.sort Task)) =>
forall tsk : Equality.sort Task,
is_true (tsk \in ts) -> nondecreasing_sequence (@task_preemption_points Task H0 tsk)
     : forall {Task : TaskType}, TaskPreemptionPoints Task -> TaskSet (Equality.sort Task) -> Prop

Arguments nondecreasing_task_preemption_points {Task H0} ts
```

## Lean

```lean
@Prosa.Model.Task.Preemption.LimitedPreemptive.nondecreasing_task_preemption_points : {Task :
    Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Preemption.Parameters.TaskPreemptionPoints Task] → Prosa.Model.Task.Concept.TaskSet Task → Prop
```

Body:

```lean
def Prosa.Model.Task.Preemption.LimitedPreemptive.nondecreasing_task_preemption_points.{u_1} : {Task :
    Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Preemption.Parameters.TaskPreemptionPoints Task] → Prosa.Model.Task.Concept.TaskSet Task → Prop :=
fun {Task} [DecidableEq Task] [Prosa.Model.Task.Preemption.Parameters.TaskPreemptionPoints Task] ts =>
  ∀ (tsk : Task),
    decide (tsk ∈ ts) = true →
      Prosa.Util.Nondecreasing.nondecreasing_sequence
        (Prosa.Model.Task.Preemption.Parameters.task_preemption_points tsk)
```

## Lean, imported into Rocq

```coq
Prosa_Model_Task_Preemption_LimitedPreemptive_nondecreasing_task_preemption_points
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task),
       Prosa_Model_Task_Preemption_Parameters_TaskPreemptionPoints Task
         inst_3 ->
       Prosa_Model_Task_Concept_TaskSet Task -> SProp
```

Body:

```coq
Prosa_Model_Task_Preemption_LimitedPreemptive_nondecreasing_task_preemption_points@{u_1 Lean.u_1+1.0
Lean.u_1+2.0} =
fun (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_3 : DecidableEq Task)
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
Prosa_Util_Nondecreasing_nondecreasing_sequence
  (Prosa_Model_Task_Preemption_Parameters_TaskPreemptionPoints_task_preemption_points Task
     inst_3
     inst_9 tsk)
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task),
       Prosa_Model_Task_Preemption_Parameters_TaskPreemptionPoints Task
         inst_3 ->
       Prosa_Model_Task_Concept_TaskSet Task -> SProp

Arguments Prosa_Model_Task_Preemption_LimitedPreemptive_nondecreasing_task_preemption_points 
  Task inst_3
  inst_9 
  ts
```
