# `task_rbf`

- Kind (Rocq): Definition
- Rocq: `prosa.implementation.refinements.arrival_curve.task_rbf`
- Lean: `Prosa.Implementation.Refinements.ArrivalCurve.task_rbf`
- Certificate: `task_rbf_correspondence`

## Official Rocq

```coq
task_rbf : Equality.sort Task -> duration -> nat

task_rbf is not universe polymorphic
Arguments task_rbf tsk Δ
task_rbf is transparent
Expands to: Constant prosa.implementation.refinements.arrival_curve.task_rbf
Declared in library prosa.implementation.refinements.arrival_curve, line 28, characters 11-19
task_rbf
     : Equality.sort Task -> duration -> nat
```

Body:

```coq
task_rbf =
fun tsk : Equality.sort Task => [eta @task_request_bound_function Task TaskCost ConcreteMaxArrivals tsk]
     : Equality.sort Task -> duration -> nat

Arguments task_rbf tsk Δ
```

## Lean

```lean
Prosa.Implementation.Refinements.ArrivalCurve.task_rbf : Prosa.Implementation.Refinements.Task.Task →
  Prosa.Behavior.Time.duration → ℕ
```

Body:

```lean
def Prosa.Implementation.Refinements.ArrivalCurve.task_rbf : Prosa.Implementation.Refinements.Task.Task →
  Prosa.Behavior.Time.duration → ℕ :=
fun tsk Δ => Prosa.Analysis.Definitions.RequestBoundFunction.task_request_bound_function tsk Δ
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_ArrivalCurve_task_rbf
     : Prosa_Implementation_Refinements_Task_Task -> Prosa_Behavior_Time_duration -> Nat
```

Body:

```coq
Prosa_Implementation_Refinements_ArrivalCurve_task_rbf@{} =
fun (tsk : Prosa_Implementation_Refinements_Task_Task) (_UU0394_ : Prosa_Behavior_Time_duration) =>
Prosa_Analysis_Definitions_RequestBoundFunction_task_request_bound_function_inst1
  Prosa_Implementation_Refinements_Task_Task
  Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_task
  Prosa_Implementation_Definitions_Task_TaskCost Prosa_Implementation_Definitions_Task_ConcreteMaxArrivals
  tsk _UU0394_
     : Prosa_Implementation_Refinements_Task_Task -> Prosa_Behavior_Time_duration -> Nat

Arguments Prosa_Implementation_Refinements_ArrivalCurve_task_rbf tsk t
```
