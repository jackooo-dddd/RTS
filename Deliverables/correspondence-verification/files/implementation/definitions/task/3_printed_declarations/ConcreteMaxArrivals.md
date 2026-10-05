# `ConcreteMaxArrivals`

- Kind (Rocq): Instance
- Rocq: `prosa.implementation.definitions.task.ConcreteMaxArrivals`
- Lean: `Prosa.Implementation.Definitions.Task.ConcreteMaxArrivals`
- Certificate: `ConcreteMaxArrivals_correspondence`

## Official Rocq

```coq
ConcreteMaxArrivals :
MaxArrivals (@reverse_coercion eqType Type task_concrete_task__canonical__eqtype_Equality concrete_task)

ConcreteMaxArrivals is not universe polymorphic
ConcreteMaxArrivals is transparent
Expands to: Constant prosa.implementation.definitions.task.ConcreteMaxArrivals
Declared in library prosa.implementation.definitions.task, line 138, characters 2-93
ConcreteMaxArrivals
     : MaxArrivals
         (@reverse_coercion eqType Type task_concrete_task__canonical__eqtype_Equality concrete_task)
```

Body:

```coq
ConcreteMaxArrivals =
let Task := @reverse_coercion eqType Type task_concrete_task__canonical__eqtype_Equality concrete_task in
concrete_max_arrivals
     : MaxArrivals
         (@reverse_coercion eqType Type task_concrete_task__canonical__eqtype_Equality concrete_task)
```

## Lean

```lean
Prosa.Implementation.Definitions.Task.ConcreteMaxArrivals : Prosa.Model.Task.Arrival.Curves.MaxArrivals
  Prosa.Implementation.Definitions.Task.concrete_task
```

Body:

```lean
@[instance_reducible] def Prosa.Implementation.Definitions.Task.ConcreteMaxArrivals : Prosa.Model.Task.Arrival.Curves.MaxArrivals
  Prosa.Implementation.Definitions.Task.concrete_task :=
{ max_arrivals := Prosa.Implementation.Definitions.Task.concrete_max_arrivals }
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Definitions_Task_ConcreteMaxArrivals
     : Prosa_Model_Task_Arrival_Curves_MaxArrivals_inst1 Prosa_Implementation_Definitions_Task_concrete_task
         Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_task
```

Body:

```coq
Prosa_Implementation_Definitions_Task_ConcreteMaxArrivals@{} =
Prosa_Model_Task_Arrival_Curves_MaxArrivals_mk_inst1 Prosa_Implementation_Definitions_Task_concrete_task
  Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_task
  Prosa_Implementation_Definitions_Task_concrete_max_arrivals
     : Prosa_Model_Task_Arrival_Curves_MaxArrivals_inst1 Prosa_Implementation_Definitions_Task_concrete_task
         Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_task
```
