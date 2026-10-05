# `total_ohep_rbf_T`

- Kind (Rocq): Definition
- Rocq: `prosa.implementation.refinements.FP.refinements.total_ohep_rbf_T`
- Lean: `Prosa.Implementation.Refinements.FP.Refinements.total_ohep_rbf_T`
- Certificate: `total_ohep_rbf_T_correspondence`

## Official Rocq

```coq
total_ohep_rbf_T :
forall {T : Type},
zero_of T ->
one_of T ->
add_of T ->
mul_of T -> div_of T -> mod_of T -> leq_of T -> eq_of (@task_T T) -> seq (@task_T T) -> @task_T T -> T -> T

total_ohep_rbf_T is not universe polymorphic
Arguments total_ohep_rbf_T {T}%_type_scope {zero_of0 one_of0 add_of0 mul_of0 div_of0 mod_of0 leq_of0 eq_of2}
  ts%_seq_scope tsk Δ
total_ohep_rbf_T is transparent
Expands to: Constant prosa.implementation.refinements.FP.refinements.total_ohep_rbf_T
Declared in library prosa.implementation.refinements.FP.refinements, line 34, characters 13-29
@total_ohep_rbf_T
     : forall T : Type,
       zero_of T ->
       one_of T ->
       add_of T ->
       mul_of T ->
       div_of T -> mod_of T -> leq_of T -> eq_of (@task_T T) -> seq (@task_T T) -> @task_T T -> T -> T
```

Body:

```coq
total_ohep_rbf_T =
fun (T : Type) (zero_of0 : zero_of T) (one_of0 : one_of T) (add_of0 : add_of T) (mul_of0 : mul_of T)
  (div_of0 : div_of T) (mod_of0 : mod_of T) (leq_of0 : leq_of T) (eq_of2 : eq_of (@task_T T))
  (ts : seq (@task_T T)) (tsk : @task_T T) (Δ : T) =>
let hep_ts := [seq tsk' <- ts | @ohep_task_T T leq_of0 eq_of2 tsk' tsk] in
let work_ts :=
  [seq @task_rbf_T T zero_of0 one_of0 add_of0 mul_of0 div_of0 mod_of0 leq_of0 tsk' Δ | tsk' <- hep_ts] in
@foldr T T +%C 0%C work_ts
     : forall {T : Type},
       zero_of T ->
       one_of T ->
       add_of T ->
       mul_of T ->
       div_of T -> mod_of T -> leq_of T -> eq_of (@task_T T) -> seq (@task_T T) -> @task_T T -> T -> T

Arguments total_ohep_rbf_T {T}%_type_scope {zero_of0 one_of0 add_of0 mul_of0 div_of0 mod_of0 leq_of0 eq_of2}
  ts%_seq_scope tsk Δ
```

## Lean

```lean
@Prosa.Implementation.Refinements.FP.Refinements.total_ohep_rbf_T : {T : Type} →
  [Prosa.Implementation.Refinements.Refinements.zero_of T] →
    [Prosa.Implementation.Refinements.Refinements.one_of T] →
      [Prosa.Implementation.Refinements.Refinements.add_of T] →
        [Prosa.Implementation.Refinements.Refinements.mul_of T] →
          [Prosa.Implementation.Refinements.Refinements.div_of T] →
            [Prosa.Implementation.Refinements.Refinements.mod_of T] →
              [Prosa.Implementation.Refinements.Refinements.leq_of T] →
                [eq_of2 :
                    Prosa.Implementation.Refinements.Refinements.eq_of
                      (Prosa.Implementation.Refinements.Task.task_T T)] →
                  List (Prosa.Implementation.Refinements.Task.task_T T) →
                    Prosa.Implementation.Refinements.Task.task_T T → T → T
```

Body:

```lean
def Prosa.Implementation.Refinements.FP.Refinements.total_ohep_rbf_T : {T : Type} →
  [Prosa.Implementation.Refinements.Refinements.zero_of T] →
    [Prosa.Implementation.Refinements.Refinements.one_of T] →
      [Prosa.Implementation.Refinements.Refinements.add_of T] →
        [Prosa.Implementation.Refinements.Refinements.mul_of T] →
          [Prosa.Implementation.Refinements.Refinements.div_of T] →
            [Prosa.Implementation.Refinements.Refinements.mod_of T] →
              [Prosa.Implementation.Refinements.Refinements.leq_of T] →
                [eq_of2 :
                    Prosa.Implementation.Refinements.Refinements.eq_of
                      (Prosa.Implementation.Refinements.Task.task_T T)] →
                  List (Prosa.Implementation.Refinements.Task.task_T T) →
                    Prosa.Implementation.Refinements.Task.task_T T → T → T :=
fun {T} [Prosa.Implementation.Refinements.Refinements.zero_of T] [Prosa.Implementation.Refinements.Refinements.one_of T]
    [Prosa.Implementation.Refinements.Refinements.add_of T] [Prosa.Implementation.Refinements.Refinements.mul_of T]
    [Prosa.Implementation.Refinements.Refinements.div_of T] [Prosa.Implementation.Refinements.Refinements.mod_of T]
    [Prosa.Implementation.Refinements.Refinements.leq_of T]
    [Prosa.Implementation.Refinements.Refinements.eq_of (Prosa.Implementation.Refinements.Task.task_T T)] ts tsk Δ =>
  have hep_ts := List.filter (fun tsk' => Prosa.Implementation.Refinements.FP.Refinements.ohep_task_T tsk' tsk) ts;
  have work_ts := List.map (fun tsk' => Prosa.Implementation.Refinements.Task.task_rbf_T tsk' Δ) hep_ts;
  List.foldr Prosa.Implementation.Refinements.Refinements.add_op Prosa.Implementation.Refinements.Refinements.zero_op
    work_ts
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_FP_Refinements_total_ohep_rbf_T
     : forall T : Type,
       Prosa_Implementation_Refinements_Refinements_zero_of T ->
       Prosa_Implementation_Refinements_Refinements_one_of T ->
       Prosa_Implementation_Refinements_Refinements_add_of T ->
       Prosa_Implementation_Refinements_Refinements_mul_of T ->
       Prosa_Implementation_Refinements_Refinements_div_of T ->
       Prosa_Implementation_Refinements_Refinements_mod_of T ->
       Prosa_Implementation_Refinements_Refinements_leq_of T ->
       Prosa_Implementation_Refinements_Refinements_eq_of (Prosa_Implementation_Refinements_Task_task_T T) ->
       List_inst1 (Prosa_Implementation_Refinements_Task_task_T T) ->
       Prosa_Implementation_Refinements_Task_task_T T -> T -> T
```

Body:

```coq
Prosa_Implementation_Refinements_FP_Refinements_total_ohep_rbf_T@{} =
fun (T : Type)
  (inst_3 : 
   Prosa_Implementation_Refinements_Refinements_zero_of T)
  (inst_6 : 
   Prosa_Implementation_Refinements_Refinements_one_of T)
  (inst_9 : 
   Prosa_Implementation_Refinements_Refinements_add_of T)
  (inst_12 : 
   Prosa_Implementation_Refinements_Refinements_mul_of T)
  (inst_15 : 
   Prosa_Implementation_Refinements_Refinements_div_of T)
  (inst_18 : 
   Prosa_Implementation_Refinements_Refinements_mod_of T)
  (inst_21 : 
   Prosa_Implementation_Refinements_Refinements_leq_of T)
  (eq_of2 : Prosa_Implementation_Refinements_Refinements_eq_of
              (Prosa_Implementation_Refinements_Task_task_T T))
  (ts : List_inst1 (Prosa_Implementation_Refinements_Task_task_T T))
  (tsk : Prosa_Implementation_Refinements_Task_task_T T) (_UU0394_ : T) =>
let hep_ts :=
  List_filter_inst1 (Prosa_Implementation_Refinements_Task_task_T T)
    (fun tsk' : Prosa_Implementation_Refinements_Task_task_T T =>
     Prosa_Implementation_Refinements_FP_Refinements_ohep_task_T T
       inst_21 eq_of2 tsk' tsk)
    ts
  in
let work_ts :=
  List_map_inst3 (Prosa_Implementation_Refinements_Task_task_T T) T
    (fun tsk' : Prosa_Implementation_Refinements_Task_task_T T =>
     Prosa_Implementation_Refinements_Task_task_rbf_T T
       inst_3
       inst_6
       inst_9
       inst_12
       inst_15
       inst_18
       inst_21 tsk' _UU0394_)
    hep_ts
  in
List_foldr_inst3 T T
  (Prosa_Implementation_Refinements_Refinements_add_of_add_op T
     inst_9)
  (Prosa_Implementation_Refinements_Refinements_zero_of_zero_op T
     inst_3)
  work_ts
     : forall T : Type,
       Prosa_Implementation_Refinements_Refinements_zero_of T ->
       Prosa_Implementation_Refinements_Refinements_one_of T ->
       Prosa_Implementation_Refinements_Refinements_add_of T ->
       Prosa_Implementation_Refinements_Refinements_mul_of T ->
       Prosa_Implementation_Refinements_Refinements_div_of T ->
       Prosa_Implementation_Refinements_Refinements_mod_of T ->
       Prosa_Implementation_Refinements_Refinements_leq_of T ->
       Prosa_Implementation_Refinements_Refinements_eq_of (Prosa_Implementation_Refinements_Task_task_T T) ->
       List_inst1 (Prosa_Implementation_Refinements_Task_task_T T) ->
       Prosa_Implementation_Refinements_Task_task_T T -> T -> T

Arguments Prosa_Implementation_Refinements_FP_Refinements_total_ohep_rbf_T T%_type_scope
  inst_3
  inst_6
  inst_9
  inst_12
  inst_15
  inst_18
  inst_21 
  eq_of2 ts tsk _UU0394_
```
