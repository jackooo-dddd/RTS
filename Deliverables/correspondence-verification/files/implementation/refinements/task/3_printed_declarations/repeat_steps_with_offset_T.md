# `repeat_steps_with_offset_T`

- Kind (Rocq): Definition
- Rocq: `prosa.implementation.refinements.task.repeat_steps_with_offset_T`
- Lean: `Prosa.Implementation.Refinements.Task.repeat_steps_with_offset_T`
- Certificate: `repeat_steps_with_offset_T_correspondence`

## Official Rocq

```coq
repeat_steps_with_offset_T : forall {T : Type}, one_of T -> add_of T -> @task_T T -> seq T -> seq T

repeat_steps_with_offset_T is not universe polymorphic
Arguments repeat_steps_with_offset_T {T}%_type_scope {one_of0 add_of0} tsk offsets%_seq_scope
repeat_steps_with_offset_T is transparent
Expands to: Constant prosa.implementation.refinements.task.repeat_steps_with_offset_T
Declared in library prosa.implementation.refinements.task, line 93, characters 13-39
@repeat_steps_with_offset_T
     : forall T : Type, one_of T -> add_of T -> @task_T T -> seq T -> seq T
```

Body:

```coq
repeat_steps_with_offset_T =
fun (T : Type) (one_of0 : one_of T) (add_of0 : add_of T) (tsk : @task_T T) (offsets : seq T) =>
@flatten T [seq @time_steps_with_offset_T T one_of0 add_of0 tsk i | i <- offsets]
     : forall {T : Type}, one_of T -> add_of T -> @task_T T -> seq T -> seq T

Arguments repeat_steps_with_offset_T {T}%_type_scope {one_of0 add_of0} tsk offsets%_seq_scope
```

## Lean

```lean
@Prosa.Implementation.Refinements.Task.repeat_steps_with_offset_T : {T : Type} →
  [Prosa.Implementation.Refinements.Refinements.one_of T] →
    [Prosa.Implementation.Refinements.Refinements.add_of T] →
      Prosa.Implementation.Refinements.Task.task_T T → List T → List T
```

Body:

```lean
def Prosa.Implementation.Refinements.Task.repeat_steps_with_offset_T : {T : Type} →
  [Prosa.Implementation.Refinements.Refinements.one_of T] →
    [Prosa.Implementation.Refinements.Refinements.add_of T] →
      Prosa.Implementation.Refinements.Task.task_T T → List T → List T :=
fun {T} [Prosa.Implementation.Refinements.Refinements.one_of T] [Prosa.Implementation.Refinements.Refinements.add_of T]
    tsk offsets =>
  (List.map (Prosa.Implementation.Refinements.Task.time_steps_with_offset_T tsk) offsets).flatten
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_Task_repeat_steps_with_offset_T
     : forall T : Type,
       Prosa_Implementation_Refinements_Refinements_one_of T ->
       Prosa_Implementation_Refinements_Refinements_add_of T ->
       Prosa_Implementation_Refinements_Task_task_T T -> List_inst1 T -> List_inst1 T
```

Body:

```coq
Prosa_Implementation_Refinements_Task_repeat_steps_with_offset_T@{} =
fun (T : Type)
  (inst_3 : Prosa_Implementation_Refinements_Refinements_one_of
                                                                                T)
  (inst_6 : Prosa_Implementation_Refinements_Refinements_add_of
                                                                                T)
  (tsk : Prosa_Implementation_Refinements_Task_task_T T) (offsets : List_inst1 T) =>
List_flatten_inst1 T
  (List_map_inst3 T (List_inst1 T)
     (Prosa_Implementation_Refinements_Task_time_steps_with_offset_T T
        inst_3
        inst_6 tsk)
     offsets)
     : forall T : Type,
       Prosa_Implementation_Refinements_Refinements_one_of T ->
       Prosa_Implementation_Refinements_Refinements_add_of T ->
       Prosa_Implementation_Refinements_Task_task_T T -> List_inst1 T -> List_inst1 T

Arguments Prosa_Implementation_Refinements_Task_repeat_steps_with_offset_T T%_type_scope
  inst_3
  inst_6 tsk offsets
```
