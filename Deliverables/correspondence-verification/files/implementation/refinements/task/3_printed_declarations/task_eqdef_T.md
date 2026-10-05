# `task_eqdef_T`

- Kind (Rocq): Definition
- Rocq: `prosa.implementation.refinements.task.task_eqdef_T`
- Lean: `Prosa.Implementation.Refinements.Task.task_eqdef_T`
- Certificate: `task_eqdef_T_correspondence`

## Official Rocq

```coq
task_eqdef_T :
forall {T : Type}, eq_of T -> eq_of (@task_arrivals_bound_T T) -> @task_T T -> @task_T T -> bool

task_eqdef_T is not universe polymorphic
Arguments task_eqdef_T {T}%_type_scope {eq_of0 eq_of2} t1 t2
task_eqdef_T is transparent
Expands to: Constant prosa.implementation.refinements.task.task_eqdef_T
Declared in library prosa.implementation.refinements.task, line 40, characters 13-25
@task_eqdef_T
     : forall T : Type, eq_of T -> eq_of (@task_arrivals_bound_T T) -> @task_T T -> @task_T T -> bool
```

Body:

```coq
task_eqdef_T =
fun (T : Type) (eq_of0 : eq_of T) (eq_of2 : eq_of (@task_arrivals_bound_T T)) (t1 t2 : @task_T T) =>
(@task_id_T T t1 == @task_id_T T t2)%C && (@task_cost_T T t1 == @task_cost_T T t2)%C &&
(@task_arrival_T T t1 == @task_arrival_T T t2)%C && (@task_deadline_T T t1 == @task_deadline_T T t2)%C &&
(@task_priority_T T t1 == @task_priority_T T t2)%C
     : forall {T : Type}, eq_of T -> eq_of (@task_arrivals_bound_T T) -> @task_T T -> @task_T T -> bool

Arguments task_eqdef_T {T}%_type_scope {eq_of0 eq_of2} t1 t2
```

## Lean

```lean
@Prosa.Implementation.Refinements.Task.task_eqdef_T : {T : Type} →
  [Prosa.Implementation.Refinements.Refinements.eq_of T] →
    [Prosa.Implementation.Refinements.Refinements.eq_of
          (Prosa.Implementation.Refinements.ArrivalBound.task_arrivals_bound_T T)] →
      Prosa.Implementation.Refinements.Task.task_T T → Prosa.Implementation.Refinements.Task.task_T T → Bool
```

Body:

```lean
def Prosa.Implementation.Refinements.Task.task_eqdef_T : {T : Type} →
  [Prosa.Implementation.Refinements.Refinements.eq_of T] →
    [Prosa.Implementation.Refinements.Refinements.eq_of
          (Prosa.Implementation.Refinements.ArrivalBound.task_arrivals_bound_T T)] →
      Prosa.Implementation.Refinements.Task.task_T T → Prosa.Implementation.Refinements.Task.task_T T → Bool :=
fun {T} [Prosa.Implementation.Refinements.Refinements.eq_of T]
    [Prosa.Implementation.Refinements.Refinements.eq_of
        (Prosa.Implementation.Refinements.ArrivalBound.task_arrivals_bound_T T)]
    t1 t2 =>
  Prosa.Implementation.Refinements.Refinements.eq_op t1.task_id_T t2.task_id_T &&
          Prosa.Implementation.Refinements.Refinements.eq_op t1.task_cost_T t2.task_cost_T &&
        Prosa.Implementation.Refinements.Refinements.eq_op t1.task_arrival_T t2.task_arrival_T &&
      Prosa.Implementation.Refinements.Refinements.eq_op t1.task_deadline_T t2.task_deadline_T &&
    Prosa.Implementation.Refinements.Refinements.eq_op t1.task_priority_T t2.task_priority_T
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_Task_task_eqdef_T
     : forall T : Type,
       Prosa_Implementation_Refinements_Refinements_eq_of T ->
       Prosa_Implementation_Refinements_Refinements_eq_of
         (Prosa_Implementation_Refinements_ArrivalBound_task_arrivals_bound_T T) ->
       Prosa_Implementation_Refinements_Task_task_T T ->
       Prosa_Implementation_Refinements_Task_task_T T -> Bool
```

Body:

```coq
Prosa_Implementation_Refinements_Task_task_eqdef_T@{} =
fun (T : Type)
  (inst_3 : Prosa_Implementation_Refinements_Refinements_eq_of
                                                                                T)
  (inst_6 : Prosa_Implementation_Refinements_Refinements_eq_of
                                                                                (Prosa_Implementation_Refinements_ArrivalBound_task_arrivals_bound_T
                                                                                T))
  (t1 t2 : Prosa_Implementation_Refinements_Task_task_T T) =>
Bool_and
  (Bool_and
     (Bool_and
        (Bool_and
           (Prosa_Implementation_Refinements_Refinements_eq_of_eq_op T
              inst_3
              (Prosa_Implementation_Refinements_Task_task_T_task_id_T T t1)
              (Prosa_Implementation_Refinements_Task_task_T_task_id_T T t2))
           (Prosa_Implementation_Refinements_Refinements_eq_of_eq_op T
              inst_3
              (Prosa_Implementation_Refinements_Task_task_T_task_cost_T T t1)
              (Prosa_Implementation_Refinements_Task_task_T_task_cost_T T t2)))
        (Prosa_Implementation_Refinements_Refinements_eq_of_eq_op
           (Prosa_Implementation_Refinements_ArrivalBound_task_arrivals_bound_T T)
           inst_6
           (Prosa_Implementation_Refinements_Task_task_T_task_arrival_T T t1)
           (Prosa_Implementation_Refinements_Task_task_T_task_arrival_T T t2)))
     (Prosa_Implementation_Refinements_Refinements_eq_of_eq_op T
        inst_3
        (Prosa_Implementation_Refinements_Task_task_T_task_deadline_T T t1)
        (Prosa_Implementation_Refinements_Task_task_T_task_deadline_T T t2)))
  (Prosa_Implementation_Refinements_Refinements_eq_of_eq_op T
     inst_3
     (Prosa_Implementation_Refinements_Task_task_T_task_priority_T T t1)
     (Prosa_Implementation_Refinements_Task_task_T_task_priority_T T t2))
     : forall T : Type,
       Prosa_Implementation_Refinements_Refinements_eq_of T ->
       Prosa_Implementation_Refinements_Refinements_eq_of
         (Prosa_Implementation_Refinements_ArrivalBound_task_arrivals_bound_T T) ->
       Prosa_Implementation_Refinements_Task_task_T T ->
       Prosa_Implementation_Refinements_Task_task_T T -> Bool

Arguments Prosa_Implementation_Refinements_Task_task_eqdef_T T%_type_scope
  inst_3
  inst_6 t1 t2
```
