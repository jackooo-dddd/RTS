# `valid_taskset_arrival_curve`

- Kind (Rocq): Definition
- Rocq: `prosa.model.task.arrival.curves.valid_taskset_arrival_curve`
- Lean: `Prosa.Model.Task.Arrival.Curves.valid_taskset_arrival_curve`
- Certificate: `valid_taskset_arrival_curve_correspondence`

## Official Rocq

```coq
valid_taskset_arrival_curve :
forall {Task : TaskType}, TaskSet (Equality.sort Task) -> (Equality.sort Task -> duration -> nat) -> Prop

valid_taskset_arrival_curve is not universe polymorphic
Arguments valid_taskset_arrival_curve {Task} ts arrivals%function_scope
valid_taskset_arrival_curve is transparent
Expands to: Constant prosa.model.task.arrival.curves.valid_taskset_arrival_curve
Declared in library prosa.model.task.arrival.curves, line 131, characters 13-40
@valid_taskset_arrival_curve
     : forall Task : TaskType,
       TaskSet (Equality.sort Task) -> (Equality.sort Task -> duration -> nat) -> Prop
```

Body:

```coq
valid_taskset_arrival_curve =
fun (Task : TaskType) (ts : TaskSet (Equality.sort Task)) (arrivals : Equality.sort Task -> duration -> nat) =>
forall tsk : Equality.sort Task, is_true (tsk \in ts) -> valid_arrival_curve (arrivals tsk)
     : forall {Task : TaskType},
       TaskSet (Equality.sort Task) -> (Equality.sort Task -> duration -> nat) -> Prop

Arguments valid_taskset_arrival_curve {Task} ts arrivals%function_scope
```

## Lean

```lean
@Prosa.Model.Task.Arrival.Curves.valid_taskset_arrival_curve : {Task : Prosa.Model.Task.Concept.TaskType} →
  [DecidableEq Task] → Prosa.Model.Task.Concept.TaskSet Task → (Task → Prosa.Behavior.Time.duration → ℕ) → Prop
def Prosa.Model.Task.Arrival.Curves.valid_taskset_arrival_curve.{u_1} : {Task : Prosa.Model.Task.Concept.TaskType} →
  [DecidableEq Task] → Prosa.Model.Task.Concept.TaskSet Task → (Task → Prosa.Behavior.Time.duration → ℕ) → Prop :=
fun {Task} [DecidableEq Task] ts arrivals =>
  ∀ (tsk : Task), decide (tsk ∈ ts) = true → Prosa.Model.Task.Arrival.Curves.valid_arrival_curve (arrivals tsk)
```

## Lean, imported into Rocq

```coq
Prosa_Model_Task_Arrival_Curves_valid_taskset_arrival_curve
     : forall Task : Prosa_Model_Task_Concept_TaskType,
       DecidableEq Task ->
       Prosa_Model_Task_Concept_TaskSet Task -> (Task -> Prosa_Behavior_Time_duration -> Nat) -> SProp
```

Body:

```coq
Prosa_Model_Task_Arrival_Curves_valid_taskset_arrival_curve@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_3 : DecidableEq Task)
  (ts : Prosa_Model_Task_Concept_TaskSet Task) (arrivals : Task -> Prosa_Behavior_Time_duration -> Nat) =>
forall tsk : Task,
@eq Bool
  (Decidable_decide
     (Membership_mem Task (Prosa_Model_Task_Concept_TaskSet Task) (List_instMembership Task) ts tsk)
     (List_instDecidableMemOfLawfulBEq Task
        (instBEqOfDecidableEq Task inst_3)
        (instLawfulBEq Task inst_3) tsk ts))
  Bool_true ->
Prosa_Model_Task_Arrival_Curves_valid_arrival_curve (arrivals tsk)
     : forall Task : Prosa_Model_Task_Concept_TaskType,
       DecidableEq Task ->
       Prosa_Model_Task_Concept_TaskSet Task -> (Task -> Prosa_Behavior_Time_duration -> Nat) -> SProp

Arguments Prosa_Model_Task_Arrival_Curves_valid_taskset_arrival_curve Task
  inst_3 ts arrivals%_function_scope
```
