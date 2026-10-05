# `blocking_bound_NP_T`

- Kind (Rocq): Definition
- Rocq: `prosa.implementation.refinements.EDF.refinements.blocking_bound_NP_T`
- Lean: `Prosa.Implementation.Refinements.EDF.Refinements.blocking_bound_NP_T`
- Certificate: `blocking_bound_NP_T_correspondence`

## Official Rocq

```coq
blocking_bound_NP_T :
forall {T : Type},
zero_of T ->
one_of T ->
sub_of T ->
add_of T -> mul_of T -> div_of T -> mod_of T -> leq_of T -> lt_of T -> seq (@task_T T) -> @task_T T -> T -> T

blocking_bound_NP_T is not universe polymorphic
Arguments blocking_bound_NP_T {T}%_type_scope
  {zero_of0 one_of0 sub_of0 add_of0 mul_of0 div_of0 mod_of0 leq_of0 lt_of0} ts%_seq_scope 
  tsk A
blocking_bound_NP_T is transparent
Expands to: Constant prosa.implementation.refinements.EDF.refinements.blocking_bound_NP_T
Declared in library prosa.implementation.refinements.EDF.refinements, line 35, characters 13-32
@blocking_bound_NP_T
     : forall T : Type,
       zero_of T ->
       one_of T ->
       sub_of T ->
       add_of T ->
       mul_of T -> div_of T -> mod_of T -> leq_of T -> lt_of T -> seq (@task_T T) -> @task_T T -> T -> T
```

Body:

```coq
blocking_bound_NP_T =
fun (T : Type) (zero_of0 : zero_of T) (one_of0 : one_of T) (sub_of0 : sub_of T) (add_of0 : add_of T)
  (mul_of0 : mul_of T) (div_of0 : div_of T) (mod_of0 : mod_of T) (leq_of0 : leq_of T) 
  (lt_of0 : lt_of T) (ts : seq (@task_T T)) (tsk : @task_T T) (A : T) =>
let blocking_relevant :=
  fun tsk_o : @task_T T =>
  (0 < @ConcreteMaxArrivals_T T zero_of0 one_of0 add_of0 mul_of0 div_of0 mod_of0 leq_of0 tsk_o 1)%C &&
  (0 < @task_cost_T T tsk_o)%C in
let ts_lp :=
  [seq tsk_o <- ts | blocking_relevant tsk_o & (@task_deadline_T T tsk + A < @task_deadline_T T tsk_o)%C] in
let ts_block := [seq (@task_cost_T T tsk_o - 1)%C | tsk_o <- ts_lp] in
@foldr T T (@maxn_T T lt_of0) 0%C ts_block
     : forall {T : Type},
       zero_of T ->
       one_of T ->
       sub_of T ->
       add_of T ->
       mul_of T -> div_of T -> mod_of T -> leq_of T -> lt_of T -> seq (@task_T T) -> @task_T T -> T -> T

Arguments blocking_bound_NP_T {T}%_type_scope
  {zero_of0 one_of0 sub_of0 add_of0 mul_of0 div_of0 mod_of0 leq_of0 lt_of0} ts%_seq_scope 
  tsk A
```

## Lean

```lean
@Prosa.Implementation.Refinements.EDF.Refinements.blocking_bound_NP_T : {T : Type} →
  [Prosa.Implementation.Refinements.Refinements.zero_of T] →
    [Prosa.Implementation.Refinements.Refinements.one_of T] →
      [Prosa.Implementation.Refinements.Refinements.sub_of T] →
        [Prosa.Implementation.Refinements.Refinements.add_of T] →
          [Prosa.Implementation.Refinements.Refinements.mul_of T] →
            [Prosa.Implementation.Refinements.Refinements.div_of T] →
              [Prosa.Implementation.Refinements.Refinements.mod_of T] →
                [Prosa.Implementation.Refinements.Refinements.leq_of T] →
                  [Prosa.Implementation.Refinements.Refinements.lt_of T] →
                    List (Prosa.Implementation.Refinements.Task.task_T T) →
                      Prosa.Implementation.Refinements.Task.task_T T → T → T
```

Body:

```lean
def Prosa.Implementation.Refinements.EDF.Refinements.blocking_bound_NP_T : {T : Type} →
  [Prosa.Implementation.Refinements.Refinements.zero_of T] →
    [Prosa.Implementation.Refinements.Refinements.one_of T] →
      [Prosa.Implementation.Refinements.Refinements.sub_of T] →
        [Prosa.Implementation.Refinements.Refinements.add_of T] →
          [Prosa.Implementation.Refinements.Refinements.mul_of T] →
            [Prosa.Implementation.Refinements.Refinements.div_of T] →
              [Prosa.Implementation.Refinements.Refinements.mod_of T] →
                [Prosa.Implementation.Refinements.Refinements.leq_of T] →
                  [Prosa.Implementation.Refinements.Refinements.lt_of T] →
                    List (Prosa.Implementation.Refinements.Task.task_T T) →
                      Prosa.Implementation.Refinements.Task.task_T T → T → T :=
fun {T} [Prosa.Implementation.Refinements.Refinements.zero_of T] [Prosa.Implementation.Refinements.Refinements.one_of T]
    [Prosa.Implementation.Refinements.Refinements.sub_of T] [Prosa.Implementation.Refinements.Refinements.add_of T]
    [Prosa.Implementation.Refinements.Refinements.mul_of T] [Prosa.Implementation.Refinements.Refinements.div_of T]
    [Prosa.Implementation.Refinements.Refinements.mod_of T] [Prosa.Implementation.Refinements.Refinements.leq_of T]
    [Prosa.Implementation.Refinements.Refinements.lt_of T] ts tsk A =>
  have ts_lp :=
    List.filter
      (fun tsk_o =>
        Prosa.Implementation.Refinements.Refinements.lt_op Prosa.Implementation.Refinements.Refinements.zero_op
              (Prosa.Implementation.Refinements.Task.ConcreteMaxArrivals_T tsk_o
                Prosa.Implementation.Refinements.Refinements.one_op) &&
            Prosa.Implementation.Refinements.Refinements.lt_op Prosa.Implementation.Refinements.Refinements.zero_op
              tsk_o.task_cost_T &&
          Prosa.Implementation.Refinements.Refinements.lt_op
            (Prosa.Implementation.Refinements.Refinements.add_op tsk.task_deadline_T A) tsk_o.task_deadline_T)
      ts;
  have ts_block :=
    List.map
      (fun tsk_o =>
        Prosa.Implementation.Refinements.Refinements.sub_op tsk_o.task_cost_T
          Prosa.Implementation.Refinements.Refinements.one_op)
      ts_lp;
  List.foldr Prosa.Implementation.Refinements.Refinements.maxn_T Prosa.Implementation.Refinements.Refinements.zero_op
    ts_block
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_EDF_Refinements_blocking_bound_NP_T
     : forall T : Type,
       Prosa_Implementation_Refinements_Refinements_zero_of T ->
       Prosa_Implementation_Refinements_Refinements_one_of T ->
       Prosa_Implementation_Refinements_Refinements_sub_of T ->
       Prosa_Implementation_Refinements_Refinements_add_of T ->
       Prosa_Implementation_Refinements_Refinements_mul_of T ->
       Prosa_Implementation_Refinements_Refinements_div_of T ->
       Prosa_Implementation_Refinements_Refinements_mod_of T ->
       Prosa_Implementation_Refinements_Refinements_leq_of T ->
       Prosa_Implementation_Refinements_Refinements_lt_of T ->
       List_inst1 (Prosa_Implementation_Refinements_Task_task_T T) ->
       Prosa_Implementation_Refinements_Task_task_T T -> T -> T
```

Body:

```coq
Prosa_Implementation_Refinements_EDF_Refinements_blocking_bound_NP_T@{} =
fun (T : Type)
  (inst_3 : 
   Prosa_Implementation_Refinements_Refinements_zero_of T)
  (inst_6 : 
   Prosa_Implementation_Refinements_Refinements_one_of T)
  (inst_9 : 
   Prosa_Implementation_Refinements_Refinements_sub_of T)
  (inst_12 : 
   Prosa_Implementation_Refinements_Refinements_add_of T)
  (inst_15 : 
   Prosa_Implementation_Refinements_Refinements_mul_of T)
  (inst_18 : 
   Prosa_Implementation_Refinements_Refinements_div_of T)
  (inst_21 : 
   Prosa_Implementation_Refinements_Refinements_mod_of T)
  (inst_24 : 
   Prosa_Implementation_Refinements_Refinements_leq_of T)
  (inst_27 : 
   Prosa_Implementation_Refinements_Refinements_lt_of T)
  (ts : List_inst1 (Prosa_Implementation_Refinements_Task_task_T T))
  (tsk : Prosa_Implementation_Refinements_Task_task_T T) (A : T) =>
let ts_lp :=
  List_filter_inst1 (Prosa_Implementation_Refinements_Task_task_T T)
    (fun tsk_o : Prosa_Implementation_Refinements_Task_task_T T =>
     Bool_and
       (Bool_and
          (Prosa_Implementation_Refinements_Refinements_lt_of_lt_op T
             inst_27
             (Prosa_Implementation_Refinements_Refinements_zero_of_zero_op T
                inst_3)
             (Prosa_Implementation_Refinements_Task_ConcreteMaxArrivals_T T
                inst_3
                inst_6
                inst_12
                inst_15
                inst_18
                inst_21
                inst_24 tsk_o
                (Prosa_Implementation_Refinements_Refinements_one_of_one_op T
                   inst_6)))
          (Prosa_Implementation_Refinements_Refinements_lt_of_lt_op T
             inst_27
             (Prosa_Implementation_Refinements_Refinements_zero_of_zero_op T
                inst_3)
             (Prosa_Implementation_Refinements_Task_task_T_task_cost_T T tsk_o)))
       (Prosa_Implementation_Refinements_Refinements_lt_of_lt_op T
          inst_27
          (Prosa_Implementation_Refinements_Refinements_add_of_add_op T
             inst_12
             (Prosa_Implementation_Refinements_Task_task_T_task_deadline_T T tsk) A)
          (Prosa_Implementation_Refinements_Task_task_T_task_deadline_T T tsk_o)))
    ts
  in
let ts_block :=
  List_map_inst3 (Prosa_Implementation_Refinements_Task_task_T T) T
    (fun tsk_o : Prosa_Implementation_Refinements_Task_task_T T =>
     Prosa_Implementation_Refinements_Refinements_sub_of_sub_op T
       inst_9
       (Prosa_Implementation_Refinements_Task_task_T_task_cost_T T tsk_o)
       (Prosa_Implementation_Refinements_Refinements_one_of_one_op T
          inst_6))
    ts_lp
  in
List_foldr_inst3 T T
  (Prosa_Implementation_Refinements_Refinements_maxn_T T
     inst_27)
  (Prosa_Implementation_Refinements_Refinements_zero_of_zero_op T
     inst_3)
  ts_block
     : forall T : Type,
       Prosa_Implementation_Refinements_Refinements_zero_of T ->
       Prosa_Implementation_Refinements_Refinements_one_of T ->
       Prosa_Implementation_Refinements_Refinements_sub_of T ->
       Prosa_Implementation_Refinements_Refinements_add_of T ->
       Prosa_Implementation_Refinements_Refinements_mul_of T ->
       Prosa_Implementation_Refinements_Refinements_div_of T ->
       Prosa_Implementation_Refinements_Refinements_mod_of T ->
       Prosa_Implementation_Refinements_Refinements_leq_of T ->
       Prosa_Implementation_Refinements_Refinements_lt_of T ->
       List_inst1 (Prosa_Implementation_Refinements_Task_task_T T) ->
       Prosa_Implementation_Refinements_Task_task_T T -> T -> T

Arguments Prosa_Implementation_Refinements_EDF_Refinements_blocking_bound_NP_T T%_type_scope
  inst_3
  inst_6
  inst_9
  inst_12
  inst_15
  inst_18
  inst_21
  inst_24
  inst_27 
  ts tsk A
```
