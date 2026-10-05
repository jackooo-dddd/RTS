# `time_steps_with_offset_T`

- Kind (Rocq): Definition
- Rocq: `prosa.implementation.refinements.task.time_steps_with_offset_T`
- Lean: `Prosa.Implementation.Refinements.Task.time_steps_with_offset_T`
- Certificate: `time_steps_with_offset_T_correspondence`

## Official Rocq

```coq
time_steps_with_offset_T : forall {T : Type}, one_of T -> add_of T -> @task_T T -> T -> seq T

time_steps_with_offset_T is not universe polymorphic
Arguments time_steps_with_offset_T {T}%_type_scope {one_of0 add_of0} tsk δ
time_steps_with_offset_T is transparent
Expands to: Constant prosa.implementation.refinements.task.time_steps_with_offset_T
Declared in library prosa.implementation.refinements.task, line 88, characters 13-37
@time_steps_with_offset_T
     : forall T : Type, one_of T -> add_of T -> @task_T T -> T -> seq T
```

Body:

```coq
time_steps_with_offset_T =
fun (T : Type) (one_of0 : one_of T) (add_of0 : add_of T) (tsk : @task_T T) (δ : T) =>
     : forall {T : Type}, one_of T -> add_of T -> @task_T T -> T -> seq T

Arguments time_steps_with_offset_T {T}%_type_scope {one_of0 add_of0} tsk δ
```

## Lean

```lean
@Prosa.Implementation.Refinements.Task.time_steps_with_offset_T : {T : Type} →
  [Prosa.Implementation.Refinements.Refinements.one_of T] →
    [Prosa.Implementation.Refinements.Refinements.add_of T] →
      Prosa.Implementation.Refinements.Task.task_T T → T → List T
```

Body:

```lean
def Prosa.Implementation.Refinements.Task.time_steps_with_offset_T : {T : Type} →
  [Prosa.Implementation.Refinements.Refinements.one_of T] →
    [Prosa.Implementation.Refinements.Refinements.add_of T] →
      Prosa.Implementation.Refinements.Task.task_T T → T → List T :=
fun {T} [Prosa.Implementation.Refinements.Refinements.one_of T] [Prosa.Implementation.Refinements.Refinements.add_of T]
    tsk δ =>
  List.map (fun t => Prosa.Implementation.Refinements.Refinements.add_op t δ)
    (Prosa.Implementation.Refinements.Task.get_time_steps_of_task_T tsk)
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_Task_time_steps_with_offset_T
     : forall T : Type,
       Prosa_Implementation_Refinements_Refinements_one_of T ->
       Prosa_Implementation_Refinements_Refinements_add_of T ->
       Prosa_Implementation_Refinements_Task_task_T T -> T -> List_inst1 T
```

Body:

```coq
Prosa_Implementation_Refinements_Task_time_steps_with_offset_T@{} =
fun (T : Type)
  (inst_3 : Prosa_Implementation_Refinements_Refinements_one_of
                                                                                T)
  (inst_6 : Prosa_Implementation_Refinements_Refinements_add_of
                                                                                T)
  (tsk : Prosa_Implementation_Refinements_Task_task_T T) (_UU03b4_ : T) =>
List_map_inst3 T T
  (fun t : T =>
   Prosa_Implementation_Refinements_Refinements_add_of_add_op T
     inst_6 t _UU03b4_)
  (Prosa_Implementation_Refinements_Task_get_time_steps_of_task_T T
     inst_3 tsk)
     : forall T : Type,
       Prosa_Implementation_Refinements_Refinements_one_of T ->
       Prosa_Implementation_Refinements_Refinements_add_of T ->
       Prosa_Implementation_Refinements_Task_task_T T -> T -> List_inst1 T

Arguments Prosa_Implementation_Refinements_Task_time_steps_with_offset_T T%_type_scope
  inst_3
  inst_6 tsk 
  s
```
