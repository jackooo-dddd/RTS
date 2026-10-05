# `valid_periods`

- Kind (Rocq): Definition
- Rocq: `prosa.model.task.arrival.periodic.valid_periods`
- Lean: `Prosa.Model.Task.Arrival.Periodic.valid_periods`
- Certificate: `valid_periods_correspondence`

## Official Rocq

```coq
valid_periods : forall {Task : TaskType}, PeriodicModel Task -> TaskSet (Equality.sort Task) -> Prop

valid_periods is not universe polymorphic
Arguments valid_periods {Task H} ts
valid_periods is transparent
Expands to: Constant prosa.model.task.arrival.periodic.valid_periods
Declared in library prosa.model.task.arrival.periodic, line 55, characters 13-26
@valid_periods
     : forall Task : TaskType, PeriodicModel Task -> TaskSet (Equality.sort Task) -> Prop
```

Body:

```coq
valid_periods =
fun (Task : TaskType) (H : PeriodicModel Task) (ts : TaskSet (Equality.sort Task)) =>
forall tsk : Equality.sort Task, is_true (tsk \in ts) -> is_true (@valid_period Task H tsk)
     : forall {Task : TaskType}, PeriodicModel Task -> TaskSet (Equality.sort Task) -> Prop

Arguments valid_periods {Task H} ts
```

## Lean

```lean
@Prosa.Model.Task.Arrival.Periodic.valid_periods : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Arrival.Periodic.PeriodicModel Task] → Prosa.Model.Task.Concept.TaskSet Task → Prop
```

Body:

```lean
def Prosa.Model.Task.Arrival.Periodic.valid_periods.{u_1} : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Arrival.Periodic.PeriodicModel Task] → Prosa.Model.Task.Concept.TaskSet Task → Prop :=
fun {Task} [DecidableEq Task] [Prosa.Model.Task.Arrival.Periodic.PeriodicModel Task] ts =>
  ∀ (tsk : Task), decide (tsk ∈ ts) = true → Prosa.Model.Task.Arrival.Periodic.valid_period tsk = true
```

## Lean, imported into Rocq

```coq
Prosa_Model_Task_Arrival_Periodic_valid_periods
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Task_Arrival_Periodic_PeriodicModel Task
         inst_3 ->
       Prosa_Model_Task_Concept_TaskSet Task -> SProp
```

Body:

```coq
Prosa_Model_Task_Arrival_Periodic_valid_periods@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_3 : DecidableEq Task)
  (inst_6 : Prosa_Model_Task_Arrival_Periodic_PeriodicModel
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
  (Prosa_Model_Task_Arrival_Periodic_valid_period Task
     inst_3
     inst_6 tsk)
  Bool_true
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Task_Arrival_Periodic_PeriodicModel Task
         inst_3 ->
       Prosa_Model_Task_Concept_TaskSet Task -> SProp

Arguments Prosa_Model_Task_Arrival_Periodic_valid_periods Task
  inst_3
  inst_6 ts
```
