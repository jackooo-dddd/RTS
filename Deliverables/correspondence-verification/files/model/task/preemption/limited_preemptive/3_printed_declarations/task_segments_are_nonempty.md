# `task_segments_are_nonempty`

- Kind (Rocq): Definition
- Rocq: `prosa.model.task.preemption.limited_preemptive.task_segments_are_nonempty`
- Lean: `Prosa.Model.Task.Preemption.LimitedPreemptive.task_segments_are_nonempty`
- Certificate: `task_segments_are_nonempty_correspondence`

## Official Rocq

```coq
task_segments_are_nonempty :
forall {Task : TaskType}, TaskPreemptionPoints Task -> TaskSet (Equality.sort Task) -> Prop

task_segments_are_nonempty is not universe polymorphic
Arguments task_segments_are_nonempty {Task H0} ts
task_segments_are_nonempty is transparent
Expands to: Constant prosa.model.task.preemption.limited_preemptive.task_segments_are_nonempty
Declared in library prosa.model.task.preemption.limited_preemptive, line 70, characters 13-39
@task_segments_are_nonempty
     : forall Task : TaskType, TaskPreemptionPoints Task -> TaskSet (Equality.sort Task) -> Prop
```

Body:

```coq
task_segments_are_nonempty =
fun (Task : TaskType) (H0 : TaskPreemptionPoints Task) (ts : TaskSet (Equality.sort Task)) =>
forall (tsk : Equality.sort Task) (n : nat),
is_true (tsk \in ts) ->
is_true (n < @size nat (distances (@task_preemption_points Task H0 tsk))) ->
is_true (0 < @nth nat 0 (distances (@task_preemption_points Task H0 tsk)) n)
     : forall {Task : TaskType}, TaskPreemptionPoints Task -> TaskSet (Equality.sort Task) -> Prop

Arguments task_segments_are_nonempty {Task H0} ts
```

## Lean

```lean
@Prosa.Model.Task.Preemption.LimitedPreemptive.task_segments_are_nonempty : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Preemption.Parameters.TaskPreemptionPoints Task] → Prosa.Model.Task.Concept.TaskSet Task → Prop
```

Body:

```lean
def Prosa.Model.Task.Preemption.LimitedPreemptive.task_segments_are_nonempty.{u_1} : {Task :
    Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Preemption.Parameters.TaskPreemptionPoints Task] → Prosa.Model.Task.Concept.TaskSet Task → Prop :=
fun {Task} [DecidableEq Task] [Prosa.Model.Task.Preemption.Parameters.TaskPreemptionPoints Task] ts =>
  ∀ (tsk : Task) (n : ℕ),
    decide (tsk ∈ ts) = true →
      n <
          (Prosa.Util.Nondecreasing.distances
              (Prosa.Model.Task.Preemption.Parameters.task_preemption_points tsk)).length →
        1 ≤
          (Prosa.Util.Nondecreasing.distances (Prosa.Model.Task.Preemption.Parameters.task_preemption_points tsk)).getD
            n 0
```

## Lean, imported into Rocq

```coq
Prosa_Model_Task_Preemption_LimitedPreemptive_task_segments_are_nonempty
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task),
       Prosa_Model_Task_Preemption_Parameters_TaskPreemptionPoints Task
         inst_3 ->
       Prosa_Model_Task_Concept_TaskSet Task -> SProp
```

Body:

```coq
Prosa_Model_Task_Preemption_LimitedPreemptive_task_segments_are_nonempty@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_3 : DecidableEq Task)
  (inst_9 : 
   Prosa_Model_Task_Preemption_Parameters_TaskPreemptionPoints Task
     inst_3)
  (ts : Prosa_Model_Task_Concept_TaskSet Task) =>
forall (tsk : Task) (n : Nat),
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
LT_lt_inst1 Nat instLTNat n
  (List_length_inst1 Nat
     (Prosa_Util_Nondecreasing_distances
        (Prosa_Model_Task_Preemption_Parameters_TaskPreemptionPoints_task_preemption_points Task
           inst_3
           inst_9 tsk))) ->
LE_le_inst1 Nat instLENat (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1))
  (List_getD_inst1 Nat
     (Prosa_Util_Nondecreasing_distances
        (Prosa_Model_Task_Preemption_Parameters_TaskPreemptionPoints_task_preemption_points Task
           inst_3
           inst_9 tsk))
     n (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0)))
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task),
       Prosa_Model_Task_Preemption_Parameters_TaskPreemptionPoints Task
         inst_3 ->
       Prosa_Model_Task_Concept_TaskSet Task -> SProp

Arguments Prosa_Model_Task_Preemption_LimitedPreemptive_task_segments_are_nonempty 
  Task inst_3
  inst_9 
  ts
```
