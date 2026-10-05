# `task_set_with_valid_arrivals`

- Kind (Rocq): Definition
- Rocq: `prosa.implementation.refinements.arrival_curve.task_set_with_valid_arrivals`
- Lean: `Prosa.Implementation.Refinements.ArrivalCurve.task_set_with_valid_arrivals`
- Certificate: `task_set_with_valid_arrivals_correspondence`

## Official Rocq

```coq
task_set_with_valid_arrivals : seq (Equality.sort Task) -> Prop

task_set_with_valid_arrivals is not universe polymorphic
Arguments task_set_with_valid_arrivals ts%_seq_scope
task_set_with_valid_arrivals is transparent
Expands to: Constant prosa.implementation.refinements.arrival_curve.task_set_with_valid_arrivals
Declared in library prosa.implementation.refinements.arrival_curve, line 62, characters 11-39
task_set_with_valid_arrivals
     : seq (Equality.sort Task) -> Prop
```

Body:

```coq
task_set_with_valid_arrivals =
fun ts : seq (Equality.sort Task) =>
forall tsk : Equality.sort Task, is_true (tsk \in ts) -> is_true (valid_arrivals tsk)
     : seq (Equality.sort Task) -> Prop

Arguments task_set_with_valid_arrivals ts%_seq_scope
```

## Lean

```lean
Prosa.Implementation.Refinements.ArrivalCurve.task_set_with_valid_arrivals : List
    Prosa.Implementation.Refinements.Task.Task →
  Prop
```

Body:

```lean
def Prosa.Implementation.Refinements.ArrivalCurve.task_set_with_valid_arrivals : List
    Prosa.Implementation.Refinements.Task.Task →
  Prop :=
fun ts => ∀ tsk ∈ ts, Prosa.Implementation.Refinements.ArrivalCurve.valid_arrivals tsk = true
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_ArrivalCurve_task_set_with_valid_arrivals
     : List_inst1 Prosa_Implementation_Refinements_Task_Task -> SProp
```

Body:

```coq
Prosa_Implementation_Refinements_ArrivalCurve_task_set_with_valid_arrivals@{} =
fun ts : List_inst1 Prosa_Implementation_Refinements_Task_Task =>
forall tsk : Prosa_Implementation_Refinements_Task_Task,
Membership_mem_inst3 Prosa_Implementation_Refinements_Task_Task
  (List_inst1 Prosa_Implementation_Refinements_Task_Task)
  (List_instMembership_inst1 Prosa_Implementation_Refinements_Task_Task) ts tsk ->
@eq Bool (Prosa_Implementation_Refinements_ArrivalCurve_valid_arrivals tsk) Bool_true
     : List_inst1 Prosa_Implementation_Refinements_Task_Task -> SProp

Arguments Prosa_Implementation_Refinements_ArrivalCurve_task_set_with_valid_arrivals ts
```
