# `repeat_steps_with_offset`

- Kind (Rocq): Definition
- Rocq: `prosa.implementation.refinements.arrival_curve.repeat_steps_with_offset`
- Lean: `Prosa.Implementation.Refinements.ArrivalCurve.repeat_steps_with_offset`
- Certificate: `repeat_steps_with_offset_correspondence`

## Official Rocq

```coq
repeat_steps_with_offset : Equality.sort Task -> seq nat -> seq nat

repeat_steps_with_offset is not universe polymorphic
Arguments repeat_steps_with_offset tsk offsets%_seq_scope
repeat_steps_with_offset is transparent
Expands to: Constant prosa.implementation.refinements.arrival_curve.repeat_steps_with_offset
Declared in library prosa.implementation.refinements.arrival_curve, line 23, characters 11-35
repeat_steps_with_offset
     : Equality.sort Task -> seq nat -> seq nat
```

Body:

```coq
repeat_steps_with_offset =
fun (tsk : Equality.sort Task) (offsets : seq nat) =>
@flatten nat [seq time_steps_with_offset tsk i | i <- offsets]
     : Equality.sort Task -> seq nat -> seq nat

Arguments repeat_steps_with_offset tsk offsets%_seq_scope
```

## Lean

```lean
Prosa.Implementation.Refinements.ArrivalCurve.repeat_steps_with_offset : Prosa.Implementation.Refinements.Task.Task →
  List ℕ → List ℕ
```

Body:

```lean
def Prosa.Implementation.Refinements.ArrivalCurve.repeat_steps_with_offset : Prosa.Implementation.Refinements.Task.Task →
  List ℕ → List ℕ :=
fun tsk offsets => (List.map (Prosa.Implementation.Refinements.ArrivalCurve.time_steps_with_offset tsk) offsets).flatten
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_ArrivalCurve_repeat_steps_with_offset
     : Prosa_Implementation_Refinements_Task_Task -> List_inst1 Nat -> List_inst1 Nat
```

Body:

```coq
Prosa_Implementation_Refinements_ArrivalCurve_repeat_steps_with_offset@{} =
fun (tsk : Prosa_Implementation_Refinements_Task_Task) (offsets : List_inst1 Nat) =>
List_flatten_inst1 Nat
  (List_map_inst3 Nat (List_inst1 Nat)
     (Prosa_Implementation_Refinements_ArrivalCurve_time_steps_with_offset tsk) offsets)
     : Prosa_Implementation_Refinements_Task_Task -> List_inst1 Nat -> List_inst1 Nat

Arguments Prosa_Implementation_Refinements_ArrivalCurve_repeat_steps_with_offset tsk offsets
```
