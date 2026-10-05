# `bound_on_total_hep_workload_T`

- Kind (Rocq): Definition
- Rocq: `prosa.implementation.refinements.EDF.refinements.bound_on_total_hep_workload_T`
- Lean: `Prosa.Implementation.Refinements.EDF.Refinements.bound_on_total_hep_workload_T`
- Certificate: `bound_on_total_hep_workload_T_correspondence`

## Official Rocq

```coq
bound_on_total_hep_workload_T :
forall {T : Type},
zero_of T ->
one_of T ->
sub_of T ->
add_of T ->
mul_of T ->
div_of T ->
mod_of T -> leq_of T -> lt_of T -> eq_of (@task_T T) -> seq (@task_T T) -> @task_T T -> T -> T -> T

bound_on_total_hep_workload_T is not universe polymorphic
Arguments bound_on_total_hep_workload_T {T}%_type_scope
  {zero_of0 one_of0 sub_of0 add_of0 mul_of0 div_of0 mod_of0 leq_of0 lt_of0 eq_of2} 
  ts%_seq_scope tsk A Δ
bound_on_total_hep_workload_T is transparent
Expands to: Constant prosa.implementation.refinements.EDF.refinements.bound_on_total_hep_workload_T
Declared in library prosa.implementation.refinements.EDF.refinements, line 24, characters 13-42
@bound_on_total_hep_workload_T
     : forall T : Type,
       zero_of T ->
       one_of T ->
       sub_of T ->
       add_of T ->
       mul_of T ->
       div_of T ->
       mod_of T -> leq_of T -> lt_of T -> eq_of (@task_T T) -> seq (@task_T T) -> @task_T T -> T -> T -> T
```

Body:

```coq
bound_on_total_hep_workload_T =
fun (T : Type) (zero_of0 : zero_of T) (one_of0 : one_of T) (sub_of0 : sub_of T) (add_of0 : add_of T)
  (mul_of0 : mul_of T) (div_of0 : div_of T) (mod_of0 : mod_of T) (leq_of0 : leq_of T) 
  (lt_of0 : lt_of T) (eq_of2 : eq_of (@task_T T)) (ts : seq (@task_T T)) (tsk : @task_T T) 
  (A Δ : T) =>
let o_ts := [seq tsk_o <- ts | ~~ eq_of2 tsk_o tsk] in
let o_work :=
  [seq @task_rbf_T T zero_of0 one_of0 add_of0 mul_of0 div_of0 mod_of0 leq_of0 tsk_o
         (@minn_T T lt_of0 (A + 1 + @task_deadline_T T tsk - @task_deadline_T T tsk_o)%C Δ)
     | tsk_o <- o_ts]
  in
@foldr T T +%C 0%C o_work
     : forall {T : Type},
       zero_of T ->
       one_of T ->
       sub_of T ->
       add_of T ->
       mul_of T ->
       div_of T ->
       mod_of T -> leq_of T -> lt_of T -> eq_of (@task_T T) -> seq (@task_T T) -> @task_T T -> T -> T -> T

Arguments bound_on_total_hep_workload_T {T}%_type_scope
  {zero_of0 one_of0 sub_of0 add_of0 mul_of0 div_of0 mod_of0 leq_of0 lt_of0 eq_of2} 
  ts%_seq_scope tsk A Δ
```

## Lean

```lean
@Prosa.Implementation.Refinements.EDF.Refinements.bound_on_total_hep_workload_T : {T : Type} →
  [Prosa.Implementation.Refinements.Refinements.zero_of T] →
    [Prosa.Implementation.Refinements.Refinements.one_of T] →
      [Prosa.Implementation.Refinements.Refinements.sub_of T] →
        [Prosa.Implementation.Refinements.Refinements.add_of T] →
          [Prosa.Implementation.Refinements.Refinements.mul_of T] →
            [Prosa.Implementation.Refinements.Refinements.div_of T] →
              [Prosa.Implementation.Refinements.Refinements.mod_of T] →
                [Prosa.Implementation.Refinements.Refinements.leq_of T] →
                  [Prosa.Implementation.Refinements.Refinements.lt_of T] →
                    [eq_of2 :
                        Prosa.Implementation.Refinements.Refinements.eq_of
                          (Prosa.Implementation.Refinements.Task.task_T T)] →
                      List (Prosa.Implementation.Refinements.Task.task_T T) →
                        Prosa.Implementation.Refinements.Task.task_T T → T → T → T
```

Body:

```lean
def Prosa.Implementation.Refinements.EDF.Refinements.bound_on_total_hep_workload_T : {T : Type} →
  [Prosa.Implementation.Refinements.Refinements.zero_of T] →
    [Prosa.Implementation.Refinements.Refinements.one_of T] →
      [Prosa.Implementation.Refinements.Refinements.sub_of T] →
        [Prosa.Implementation.Refinements.Refinements.add_of T] →
          [Prosa.Implementation.Refinements.Refinements.mul_of T] →
            [Prosa.Implementation.Refinements.Refinements.div_of T] →
              [Prosa.Implementation.Refinements.Refinements.mod_of T] →
                [Prosa.Implementation.Refinements.Refinements.leq_of T] →
                  [Prosa.Implementation.Refinements.Refinements.lt_of T] →
                    [eq_of2 :
                        Prosa.Implementation.Refinements.Refinements.eq_of
                          (Prosa.Implementation.Refinements.Task.task_T T)] →
                      List (Prosa.Implementation.Refinements.Task.task_T T) →
                        Prosa.Implementation.Refinements.Task.task_T T → T → T → T :=
fun {T} [Prosa.Implementation.Refinements.Refinements.zero_of T] [Prosa.Implementation.Refinements.Refinements.one_of T]
    [Prosa.Implementation.Refinements.Refinements.sub_of T] [Prosa.Implementation.Refinements.Refinements.add_of T]
    [Prosa.Implementation.Refinements.Refinements.mul_of T] [Prosa.Implementation.Refinements.Refinements.div_of T]
    [Prosa.Implementation.Refinements.Refinements.mod_of T] [Prosa.Implementation.Refinements.Refinements.leq_of T]
    [Prosa.Implementation.Refinements.Refinements.lt_of T]
    [Prosa.Implementation.Refinements.Refinements.eq_of (Prosa.Implementation.Refinements.Task.task_T T)] ts tsk A Δ =>
  have o_ts := List.filter (fun tsk_o => !Prosa.Implementation.Refinements.Refinements.eq_op tsk_o tsk) ts;
  have o_work :=
    List.map
      (fun tsk_o =>
        Prosa.Implementation.Refinements.Task.task_rbf_T tsk_o
          (Prosa.Implementation.Refinements.Refinements.minn_T
            (Prosa.Implementation.Refinements.Refinements.sub_op
              (Prosa.Implementation.Refinements.Refinements.add_op
                (Prosa.Implementation.Refinements.Refinements.add_op A
                  Prosa.Implementation.Refinements.Refinements.one_op)
                tsk.task_deadline_T)
              tsk_o.task_deadline_T)
            Δ))
      o_ts;
  List.foldr Prosa.Implementation.Refinements.Refinements.add_op Prosa.Implementation.Refinements.Refinements.zero_op
    o_work
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_EDF_Refinements_bound_on_total_hep_workload_T
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
       Prosa_Implementation_Refinements_Refinements_eq_of (Prosa_Implementation_Refinements_Task_task_T T) ->
       List_inst1 (Prosa_Implementation_Refinements_Task_task_T T) ->
       Prosa_Implementation_Refinements_Task_task_T T -> T -> T -> T
```

Body:

```coq
Prosa_Implementation_Refinements_EDF_Refinements_bound_on_total_hep_workload_T@{} =
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
  (eq_of2 : Prosa_Implementation_Refinements_Refinements_eq_of
              (Prosa_Implementation_Refinements_Task_task_T T))
  (ts : List_inst1 (Prosa_Implementation_Refinements_Task_task_T T))
  (tsk : Prosa_Implementation_Refinements_Task_task_T T) (A _UU0394_ : T) =>
let o_ts :=
  List_filter_inst1 (Prosa_Implementation_Refinements_Task_task_T T)
    (fun tsk_o : Prosa_Implementation_Refinements_Task_task_T T =>
     Bool_not
       (Prosa_Implementation_Refinements_Refinements_eq_of_eq_op
          (Prosa_Implementation_Refinements_Task_task_T T) eq_of2 tsk_o tsk))
    ts
  in
let o_work :=
  List_map_inst3 (Prosa_Implementation_Refinements_Task_task_T T) T
    (fun tsk_o : Prosa_Implementation_Refinements_Task_task_T T =>
     Prosa_Implementation_Refinements_Task_task_rbf_T T
       inst_3
       inst_6
       inst_12
       inst_15
       inst_18
       inst_21
       inst_24 tsk_o
       (Prosa_Implementation_Refinements_Refinements_minn_T T
          inst_27
          (Prosa_Implementation_Refinements_Refinements_sub_of_sub_op T
             inst_9
             (Prosa_Implementation_Refinements_Refinements_add_of_add_op T
                inst_12
                (Prosa_Implementation_Refinements_Refinements_add_of_add_op T
                   inst_12 A
                   (Prosa_Implementation_Refinements_Refinements_one_of_one_op T
                      inst_6))
                (Prosa_Implementation_Refinements_Task_task_T_task_deadline_T T tsk))
             (Prosa_Implementation_Refinements_Task_task_T_task_deadline_T T tsk_o))
          _UU0394_))
    o_ts
  in
List_foldr_inst3 T T
  (Prosa_Implementation_Refinements_Refinements_add_of_add_op T
     inst_12)
  (Prosa_Implementation_Refinements_Refinements_zero_of_zero_op T
     inst_3)
  o_work
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
       Prosa_Implementation_Refinements_Refinements_eq_of (Prosa_Implementation_Refinements_Task_task_T T) ->
       List_inst1 (Prosa_Implementation_Refinements_Task_task_T T) ->
       Prosa_Implementation_Refinements_Task_task_T T -> T -> T -> T

Arguments Prosa_Implementation_Refinements_EDF_Refinements_bound_on_total_hep_workload_T 
  T%_type_scope inst_3
  inst_6
  inst_9
  inst_12
  inst_15
  inst_18
  inst_21
  inst_24
  inst_27 
  eq_of2 ts tsk A _UU0394_
```
