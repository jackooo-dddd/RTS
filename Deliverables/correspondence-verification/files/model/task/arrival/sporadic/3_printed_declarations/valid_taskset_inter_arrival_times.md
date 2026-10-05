# `valid_taskset_inter_arrival_times`

- Kind (Rocq): Definition
- Rocq: `prosa.model.task.arrival.sporadic.valid_taskset_inter_arrival_times`
- Lean: `Prosa.Model.Task.Arrival.Sporadic.valid_taskset_inter_arrival_times`
- Certificate: `sp_valid_taskset_inter_arrival_times_canonical`

## Official Rocq

```coq
valid_taskset_inter_arrival_times :
forall {Task : TaskType}, SporadicModel Task -> TaskSet (Equality.sort Task) -> Prop

valid_taskset_inter_arrival_times is not universe polymorphic
Arguments valid_taskset_inter_arrival_times {Task H} ts
valid_taskset_inter_arrival_times is transparent
Expands to: Constant prosa.model.task.arrival.sporadic.valid_taskset_inter_arrival_times
Declared in library prosa.model.task.arrival.sporadic, line 35, characters 13-46
@valid_taskset_inter_arrival_times
     : forall Task : TaskType, SporadicModel Task -> TaskSet (Equality.sort Task) -> Prop
```

Body:

```coq
valid_taskset_inter_arrival_times =
fun (Task : TaskType) (H : SporadicModel Task) (ts : TaskSet (Equality.sort Task)) =>
forall tsk : Equality.sort Task,
is_true (tsk \in ts) -> is_true (@valid_task_min_inter_arrival_time Task H tsk)
     : forall {Task : TaskType}, SporadicModel Task -> TaskSet (Equality.sort Task) -> Prop

Arguments valid_taskset_inter_arrival_times {Task H} ts
```

## Lean

```lean
@Prosa.Model.Task.Arrival.Sporadic.valid_taskset_inter_arrival_times : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Arrival.Sporadic.SporadicModel Task] → Prosa.Model.Task.Concept.TaskSet Task → Prop
def Prosa.Model.Task.Arrival.Sporadic.valid_taskset_inter_arrival_times.{u_1} : {Task :
    Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Arrival.Sporadic.SporadicModel Task] → Prosa.Model.Task.Concept.TaskSet Task → Prop :=
fun {Task} [DecidableEq Task] [Prosa.Model.Task.Arrival.Sporadic.SporadicModel Task] ts =>
  ∀ (tsk : Task),
    decide (tsk ∈ ts) = true → Prosa.Model.Task.Arrival.Sporadic.valid_task_min_inter_arrival_time tsk = true
```

## Lean, imported into Rocq

```coq
Prosa_Model_Task_Arrival_Sporadic_valid_taskset_inter_arrival_times
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Task_Arrival_Sporadic_SporadicModel Task
         inst_3 ->
       Prosa_Model_Task_Concept_TaskSet Task -> SProp
```

Body:

```coq
Prosa_Model_Task_Arrival_Sporadic_valid_taskset_inter_arrival_times@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_3 : DecidableEq Task)
  (inst_6 : Prosa_Model_Task_Arrival_Sporadic_SporadicModel
                                                                              Task
                                                                              inst_3)
  (ts : Prosa_Model_Task_Concept_TaskSet Task) =>
forall tsk : Task,
@eq Bool
  (Decidable_decide
     (Membership_mem Task (Prosa_Model_Task_Concept_TaskSet Task) (List_instMembership Task) ts tsk)
     (List_instDecidableMemOfLawfulBEq Task
        (instBEqOfDecidableEq Task inst_3)
        (instLawfulBEq Task inst_3) tsk ts))
  Bool_true ->
@eq Bool
  (Prosa_Model_Task_Arrival_Sporadic_valid_task_min_inter_arrival_time Task
     inst_3
     inst_6 tsk)
  Bool_true
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Task_Arrival_Sporadic_SporadicModel Task
         inst_3 ->
       Prosa_Model_Task_Concept_TaskSet Task -> SProp

Arguments Prosa_Model_Task_Arrival_Sporadic_valid_taskset_inter_arrival_times Task
  inst_3
  inst_6 ts
```
