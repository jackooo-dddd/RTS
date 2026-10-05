# `task_min_rbf`

- Kind (Rocq): Definition
- Rocq: `prosa.model.task.arrival.curve_as_rbf.task_min_rbf`
- Lean: `Prosa.Model.Task.Arrival.CurveAsRbf.task_min_rbf`
- Certificate: `task_min_rbf_correspondence`

## Official Rocq

```coq
task_min_rbf :
forall {Task : TaskType},
TaskMinCost Task -> (Equality.sort Task -> duration -> nat) -> Equality.sort Task -> duration -> nat

task_min_rbf is not universe polymorphic
Arguments task_min_rbf {Task H0} arrivals%function_scope task Δ
task_min_rbf is transparent
Expands to: Constant prosa.model.task.arrival.curve_as_rbf.task_min_rbf
Declared in library prosa.model.task.arrival.curve_as_rbf, line 28, characters 13-25
@task_min_rbf
     : forall Task : TaskType,
       TaskMinCost Task -> (Equality.sort Task -> duration -> nat) -> Equality.sort Task -> duration -> nat
```

Body:

```coq
task_min_rbf =
fun (Task : TaskType) (H0 : TaskMinCost Task) (arrivals : Equality.sort Task -> duration -> nat)
  (task : Equality.sort Task) (Δ : duration) =>
@task_min_cost Task H0 task * arrivals task Δ
     : forall {Task : TaskType},
       TaskMinCost Task -> (Equality.sort Task -> duration -> nat) -> Equality.sort Task -> duration -> nat

Arguments task_min_rbf {Task H0} arrivals%function_scope task Δ
```

## Lean

```lean
@Prosa.Model.Task.Arrival.CurveAsRbf.task_min_rbf : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Concept.TaskMinCost Task] →
      (Task → Prosa.Behavior.Time.duration → ℕ) → Task → Prosa.Behavior.Time.duration → ℕ
def Prosa.Model.Task.Arrival.CurveAsRbf.task_min_rbf.{u_1} : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Concept.TaskMinCost Task] →
      (Task → Prosa.Behavior.Time.duration → ℕ) → Task → Prosa.Behavior.Time.duration → ℕ :=
fun {Task} [DecidableEq Task] [Prosa.Model.Task.Concept.TaskMinCost Task] arrivals task Δ =>
  Prosa.Model.Task.Concept.task_min_cost task * arrivals task Δ
```

## Lean, imported into Rocq

```coq
Prosa_Model_Task_Arrival_CurveAsRbf_task_min_rbf
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Task_Concept_TaskMinCost Task
         inst_3 ->
       (Task -> Prosa_Behavior_Time_duration -> Nat) -> Task -> Prosa_Behavior_Time_duration -> Nat
```

Body:

```coq
Prosa_Model_Task_Arrival_CurveAsRbf_task_min_rbf@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_3 : DecidableEq Task)
  (inst_6 : Prosa_Model_Task_Concept_TaskMinCost
                                                                                Task
                                                                                inst_3)
  (arrivals : Task -> Prosa_Behavior_Time_duration -> Nat) (task : Task)
  (_UU0394_ : Prosa_Behavior_Time_duration) =>
HMul_hMul_inst7 Prosa_Behavior_Time_duration Nat Prosa_Behavior_Time_duration
  (instHMul_inst1 Prosa_Behavior_Time_duration instMulNat)
  (Prosa_Model_Task_Concept_TaskMinCost_task_min_cost Task
     inst_3
     inst_6 task)
  (arrivals task _UU0394_)
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Task_Concept_TaskMinCost Task
         inst_3 ->
       (Task -> Prosa_Behavior_Time_duration -> Nat) -> Task -> Prosa_Behavior_Time_duration -> Nat

Arguments Prosa_Model_Task_Arrival_CurveAsRbf_task_min_rbf Task
  inst_3
  inst_6 arrivals%_function_scope 
  task a____at____internal__hyg0
```
