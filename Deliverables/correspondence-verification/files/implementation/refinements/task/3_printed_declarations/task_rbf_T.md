# `task_rbf_T`

- Kind (Rocq): Definition
- Rocq: `prosa.implementation.refinements.task.task_rbf_T`
- Lean: `Prosa.Implementation.Refinements.Task.task_rbf_T`
- Certificate: `task_rbf_T_correspondence`

## Official Rocq

```coq
task_rbf_T :
forall {T : Type},
zero_of T -> one_of T -> add_of T -> mul_of T -> div_of T -> mod_of T -> leq_of T -> @task_T T -> T -> T

task_rbf_T is not universe polymorphic
Arguments task_rbf_T {T}%_type_scope {zero_of0 one_of0 add_of0 mul_of0 div_of0 mod_of0 leq_of0} tsk Δ
task_rbf_T is transparent
Expands to: Constant prosa.implementation.refinements.task.task_rbf_T
Declared in library prosa.implementation.refinements.task, line 66, characters 13-23
@task_rbf_T
     : forall T : Type,
       zero_of T ->
       one_of T -> add_of T -> mul_of T -> div_of T -> mod_of T -> leq_of T -> @task_T T -> T -> T
```

Body:

```coq
task_rbf_T =
fun (T : Type) (zero_of0 : zero_of T) (one_of0 : one_of T) (add_of0 : add_of T) (mul_of0 : mul_of T)
  (div_of0 : div_of T) (mod_of0 : mod_of T) (leq_of0 : leq_of T) (tsk : @task_T T) 
  (Δ : T) =>
(@task_cost_T T tsk * @ConcreteMaxArrivals_T T zero_of0 one_of0 add_of0 mul_of0 div_of0 mod_of0 leq_of0 tsk Δ)%C
     : forall {T : Type},
       zero_of T ->
       one_of T -> add_of T -> mul_of T -> div_of T -> mod_of T -> leq_of T -> @task_T T -> T -> T

Arguments task_rbf_T {T}%_type_scope {zero_of0 one_of0 add_of0 mul_of0 div_of0 mod_of0 leq_of0} tsk Δ
```

## Lean

```lean
@Prosa.Implementation.Refinements.Task.task_rbf_T : {T : Type} →
  [Prosa.Implementation.Refinements.Refinements.zero_of T] →
    [Prosa.Implementation.Refinements.Refinements.one_of T] →
      [Prosa.Implementation.Refinements.Refinements.add_of T] →
        [Prosa.Implementation.Refinements.Refinements.mul_of T] →
          [Prosa.Implementation.Refinements.Refinements.div_of T] →
            [Prosa.Implementation.Refinements.Refinements.mod_of T] →
              [Prosa.Implementation.Refinements.Refinements.leq_of T] →
                Prosa.Implementation.Refinements.Task.task_T T → T → T
```

Body:

```lean
def Prosa.Implementation.Refinements.Task.task_rbf_T : {T : Type} →
  [Prosa.Implementation.Refinements.Refinements.zero_of T] →
    [Prosa.Implementation.Refinements.Refinements.one_of T] →
      [Prosa.Implementation.Refinements.Refinements.add_of T] →
        [Prosa.Implementation.Refinements.Refinements.mul_of T] →
          [Prosa.Implementation.Refinements.Refinements.div_of T] →
            [Prosa.Implementation.Refinements.Refinements.mod_of T] →
              [Prosa.Implementation.Refinements.Refinements.leq_of T] →
                Prosa.Implementation.Refinements.Task.task_T T → T → T :=
fun {T} [Prosa.Implementation.Refinements.Refinements.zero_of T] [Prosa.Implementation.Refinements.Refinements.one_of T]
    [Prosa.Implementation.Refinements.Refinements.add_of T] [Prosa.Implementation.Refinements.Refinements.mul_of T]
    [Prosa.Implementation.Refinements.Refinements.div_of T] [Prosa.Implementation.Refinements.Refinements.mod_of T]
    [Prosa.Implementation.Refinements.Refinements.leq_of T] tsk Δ =>
  Prosa.Implementation.Refinements.Refinements.mul_op tsk.task_cost_T
    (Prosa.Implementation.Refinements.Task.ConcreteMaxArrivals_T tsk Δ)
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_Task_task_rbf_T
     : forall T : Type,
       Prosa_Implementation_Refinements_Refinements_zero_of T ->
       Prosa_Implementation_Refinements_Refinements_one_of T ->
       Prosa_Implementation_Refinements_Refinements_add_of T ->
       Prosa_Implementation_Refinements_Refinements_mul_of T ->
       Prosa_Implementation_Refinements_Refinements_div_of T ->
       Prosa_Implementation_Refinements_Refinements_mod_of T ->
       Prosa_Implementation_Refinements_Refinements_leq_of T ->
       Prosa_Implementation_Refinements_Task_task_T T -> T -> T
```

Body:

```coq
Prosa_Implementation_Refinements_Task_task_rbf_T@{} =
fun (T : Type)
  (inst_3 : Prosa_Implementation_Refinements_Refinements_zero_of
                                                                                T)
  (inst_6 : Prosa_Implementation_Refinements_Refinements_one_of
                                                                                T)
  (inst_9 : Prosa_Implementation_Refinements_Refinements_add_of
                                                                                T)
  (inst_12 : 
   Prosa_Implementation_Refinements_Refinements_mul_of T)
  (inst_15 : 
   Prosa_Implementation_Refinements_Refinements_div_of T)
  (inst_18 : 
   Prosa_Implementation_Refinements_Refinements_mod_of T)
  (inst_21 : 
   Prosa_Implementation_Refinements_Refinements_leq_of T)
  (tsk : Prosa_Implementation_Refinements_Task_task_T T) (_UU0394_ : T) =>
Prosa_Implementation_Refinements_Refinements_mul_of_mul_op T
  inst_12
  (Prosa_Implementation_Refinements_Task_task_T_task_cost_T T tsk)
  (Prosa_Implementation_Refinements_Task_ConcreteMaxArrivals_T T
     inst_3
     inst_6
     inst_9
     inst_12
     inst_15
     inst_18
     inst_21 tsk _UU0394_)
     : forall T : Type,
       Prosa_Implementation_Refinements_Refinements_zero_of T ->
       Prosa_Implementation_Refinements_Refinements_one_of T ->
       Prosa_Implementation_Refinements_Refinements_add_of T ->
       Prosa_Implementation_Refinements_Refinements_mul_of T ->
       Prosa_Implementation_Refinements_Refinements_div_of T ->
       Prosa_Implementation_Refinements_Refinements_mod_of T ->
       Prosa_Implementation_Refinements_Refinements_leq_of T ->
       Prosa_Implementation_Refinements_Task_task_T T -> T -> T

Arguments Prosa_Implementation_Refinements_Task_task_rbf_T T%_type_scope
  inst_3
  inst_6
  inst_9
  inst_12
  inst_15
  inst_18
  inst_21 tsk 
  _UU0394_
```
