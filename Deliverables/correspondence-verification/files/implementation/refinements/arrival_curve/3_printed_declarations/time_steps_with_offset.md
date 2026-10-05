# `time_steps_with_offset`

- Kind (Rocq): Definition
- Rocq: `prosa.implementation.refinements.arrival_curve.time_steps_with_offset`
- Lean: `Prosa.Implementation.Refinements.ArrivalCurve.time_steps_with_offset`
- Certificate: `time_steps_with_offset_correspondence`

## Official Rocq

```coq
time_steps_with_offset : Equality.sort Task -> nat -> seq nat

time_steps_with_offset is not universe polymorphic
Arguments time_steps_with_offset tsk δ%_nat_scope
time_steps_with_offset is transparent
Expands to: Constant prosa.implementation.refinements.arrival_curve.time_steps_with_offset
Declared in library prosa.implementation.refinements.arrival_curve, line 19, characters 11-33
time_steps_with_offset
     : Equality.sort Task -> nat -> seq nat
```

Body:

```coq
time_steps_with_offset =
fun (tsk : Equality.sort Task) (δ : nat) => [seq t + δ | t <- get_time_steps_of_task tsk]
     : Equality.sort Task -> nat -> seq nat

Arguments time_steps_with_offset tsk δ%_nat_scope
```

## Lean

```lean
Prosa.Implementation.Refinements.ArrivalCurve.time_steps_with_offset : Prosa.Implementation.Refinements.Task.Task →
  ℕ → List ℕ
```

Body:

```lean
def Prosa.Implementation.Refinements.ArrivalCurve.time_steps_with_offset : Prosa.Implementation.Refinements.Task.Task →
  ℕ → List ℕ :=
fun tsk δ => List.map (fun t => t + δ) (Prosa.Implementation.Refinements.ArrivalCurve.get_time_steps_of_task tsk)
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_ArrivalCurve_time_steps_with_offset
     : Prosa_Implementation_Refinements_Task_Task -> Nat -> List_inst1 Nat
```

Body:

```coq
Prosa_Implementation_Refinements_ArrivalCurve_time_steps_with_offset@{} =
fun (tsk : Prosa_Implementation_Refinements_Task_Task) (_UU03b4_ : Nat) =>
List_map_inst3 Nat Nat
  (fun t : Nat => HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat) t _UU03b4_)
  (Prosa_Implementation_Refinements_ArrivalCurve_get_time_steps_of_task tsk)
     : Prosa_Implementation_Refinements_Task_Task -> Nat -> List_inst1 Nat

Arguments Prosa_Implementation_Refinements_ArrivalCurve_time_steps_with_offset tsk s%_Nat_scope
```
