# `blocking_bound_NP_T`

- Kind (Rocq): Definition
- Rocq: `prosa.implementation.refinements.FP.refinements.blocking_bound_NP_T`
- Lean: `Prosa.Implementation.Refinements.FP.Refinements.blocking_bound_NP_T`
- Certificate: `blocking_bound_NP_T_correspondence`

## Official Rocq

```coq
blocking_bound_NP_T :
forall {T : Type},
zero_of T -> one_of T -> sub_of T -> leq_of T -> lt_of T -> seq (@task_T T) -> @task_T T -> T

blocking_bound_NP_T is not universe polymorphic
Arguments blocking_bound_NP_T {T}%_type_scope {zero_of0 one_of0 sub_of0 leq_of0 lt_of0} ts%_seq_scope tsk
blocking_bound_NP_T is transparent
Expands to: Constant prosa.implementation.refinements.FP.refinements.blocking_bound_NP_T
Declared in library prosa.implementation.refinements.FP.refinements, line 45, characters 13-32
@blocking_bound_NP_T
     : forall T : Type,
       zero_of T -> one_of T -> sub_of T -> leq_of T -> lt_of T -> seq (@task_T T) -> @task_T T -> T
```

Body:

```coq
blocking_bound_NP_T =
fun (T : Type) (zero_of0 : zero_of T) (one_of0 : one_of T) (sub_of0 : sub_of T) (leq_of0 : leq_of T)
  (lt_of0 : lt_of T) (ts : seq (@task_T T)) (tsk : @task_T T) =>
let lp_ts := [seq tsk_o <- ts | ~~ @hep_task_T T leq_of0 tsk_o tsk] in
let block_ts := [seq (@task_cost_T T tsk_o - 1)%C | tsk_o <- lp_ts] in
@foldr T T (@maxn_T T lt_of0) 0%C block_ts
     : forall {T : Type},
       zero_of T -> one_of T -> sub_of T -> leq_of T -> lt_of T -> seq (@task_T T) -> @task_T T -> T

Arguments blocking_bound_NP_T {T}%_type_scope {zero_of0 one_of0 sub_of0 leq_of0 lt_of0} ts%_seq_scope tsk
```

## Lean

```lean
@Prosa.Implementation.Refinements.FP.Refinements.blocking_bound_NP_T : {T : Type} →
  [Prosa.Implementation.Refinements.Refinements.zero_of T] →
    [Prosa.Implementation.Refinements.Refinements.one_of T] →
      [Prosa.Implementation.Refinements.Refinements.sub_of T] →
        [Prosa.Implementation.Refinements.Refinements.leq_of T] →
          [Prosa.Implementation.Refinements.Refinements.lt_of T] →
            List (Prosa.Implementation.Refinements.Task.task_T T) → Prosa.Implementation.Refinements.Task.task_T T → T
```

Body:

```lean
def Prosa.Implementation.Refinements.FP.Refinements.blocking_bound_NP_T : {T : Type} →
  [Prosa.Implementation.Refinements.Refinements.zero_of T] →
    [Prosa.Implementation.Refinements.Refinements.one_of T] →
      [Prosa.Implementation.Refinements.Refinements.sub_of T] →
        [Prosa.Implementation.Refinements.Refinements.leq_of T] →
          [Prosa.Implementation.Refinements.Refinements.lt_of T] →
            List (Prosa.Implementation.Refinements.Task.task_T T) →
              Prosa.Implementation.Refinements.Task.task_T T → T :=
fun {T} [Prosa.Implementation.Refinements.Refinements.zero_of T] [Prosa.Implementation.Refinements.Refinements.one_of T]
    [Prosa.Implementation.Refinements.Refinements.sub_of T] [Prosa.Implementation.Refinements.Refinements.leq_of T]
    [Prosa.Implementation.Refinements.Refinements.lt_of T] ts tsk =>
  have lp_ts := List.filter (fun tsk_o => !Prosa.Implementation.Refinements.FP.Refinements.hep_task_T tsk_o tsk) ts;
  have block_ts :=
    List.map
      (fun tsk_o =>
        Prosa.Implementation.Refinements.Refinements.sub_op tsk_o.task_cost_T
          Prosa.Implementation.Refinements.Refinements.one_op)
      lp_ts;
  List.foldr Prosa.Implementation.Refinements.Refinements.maxn_T Prosa.Implementation.Refinements.Refinements.zero_op
    block_ts
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_FP_Refinements_blocking_bound_NP_T
     : forall T : Type,
       Prosa_Implementation_Refinements_Refinements_zero_of T ->
       Prosa_Implementation_Refinements_Refinements_one_of T ->
       Prosa_Implementation_Refinements_Refinements_sub_of T ->
       Prosa_Implementation_Refinements_Refinements_leq_of T ->
       Prosa_Implementation_Refinements_Refinements_lt_of T ->
       List_inst1 (Prosa_Implementation_Refinements_Task_task_T T) ->
       Prosa_Implementation_Refinements_Task_task_T T -> T
```

Body:

```coq
Prosa_Implementation_Refinements_FP_Refinements_blocking_bound_NP_T@{} =
fun (T : Type)
  (inst_3 : 
   Prosa_Implementation_Refinements_Refinements_zero_of T)
  (inst_6 : 
   Prosa_Implementation_Refinements_Refinements_one_of T)
  (inst_9 : 
   Prosa_Implementation_Refinements_Refinements_sub_of T)
  (inst_12 : 
   Prosa_Implementation_Refinements_Refinements_leq_of T)
  (inst_15 : 
   Prosa_Implementation_Refinements_Refinements_lt_of T)
  (ts : List_inst1 (Prosa_Implementation_Refinements_Task_task_T T))
  (tsk : Prosa_Implementation_Refinements_Task_task_T T) =>
let lp_ts :=
  List_filter_inst1 (Prosa_Implementation_Refinements_Task_task_T T)
    (fun tsk_o : Prosa_Implementation_Refinements_Task_task_T T =>
     Bool_not
       (Prosa_Implementation_Refinements_FP_Refinements_hep_task_T T
          inst_12 tsk_o tsk))
    ts
  in
let block_ts :=
  List_map_inst3 (Prosa_Implementation_Refinements_Task_task_T T) T
    (fun tsk_o : Prosa_Implementation_Refinements_Task_task_T T =>
     Prosa_Implementation_Refinements_Refinements_sub_of_sub_op T
       inst_9
       (Prosa_Implementation_Refinements_Task_task_T_task_cost_T T tsk_o)
       (Prosa_Implementation_Refinements_Refinements_one_of_one_op T
          inst_6))
    lp_ts
  in
List_foldr_inst3 T T
  (Prosa_Implementation_Refinements_Refinements_maxn_T T
     inst_15)
  (Prosa_Implementation_Refinements_Refinements_zero_of_zero_op T
     inst_3)
  block_ts
     : forall T : Type,
       Prosa_Implementation_Refinements_Refinements_zero_of T ->
       Prosa_Implementation_Refinements_Refinements_one_of T ->
       Prosa_Implementation_Refinements_Refinements_sub_of T ->
       Prosa_Implementation_Refinements_Refinements_leq_of T ->
       Prosa_Implementation_Refinements_Refinements_lt_of T ->
       List_inst1 (Prosa_Implementation_Refinements_Task_task_T T) ->
       Prosa_Implementation_Refinements_Task_task_T T -> T

Arguments Prosa_Implementation_Refinements_FP_Refinements_blocking_bound_NP_T T%_type_scope
  inst_3
  inst_6
  inst_9
  inst_12
  inst_15 
  ts tsk
```
