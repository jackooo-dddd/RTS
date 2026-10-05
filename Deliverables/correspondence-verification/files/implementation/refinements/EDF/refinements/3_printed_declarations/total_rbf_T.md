# `total_rbf_T`

- Kind (Rocq): Definition
- Rocq: `prosa.implementation.refinements.EDF.refinements.total_rbf_T`
- Lean: `Prosa.Implementation.Refinements.EDF.Refinements.total_rbf_T`
- Certificate: `total_rbf_T_correspondence`

## Official Rocq

```coq
total_rbf_T :
forall {T : Type},
zero_of T ->
one_of T -> add_of T -> mul_of T -> div_of T -> mod_of T -> leq_of T -> seq (@task_T T) -> T -> T

total_rbf_T is not universe polymorphic
Arguments total_rbf_T {T}%_type_scope {zero_of0 one_of0 add_of0 mul_of0 div_of0 mod_of0 leq_of0}
  ts%_seq_scope Δ
total_rbf_T is transparent
Expands to: Constant prosa.implementation.refinements.EDF.refinements.total_rbf_T
Declared in library prosa.implementation.refinements.EDF.refinements, line 19, characters 13-24
@total_rbf_T
     : forall T : Type,
       zero_of T ->
       one_of T -> add_of T -> mul_of T -> div_of T -> mod_of T -> leq_of T -> seq (@task_T T) -> T -> T
```

Body:

```coq
total_rbf_T =
fun (T : Type) (zero_of0 : zero_of T) (one_of0 : one_of T) (add_of0 : add_of T) (mul_of0 : mul_of T)
  (div_of0 : div_of T) (mod_of0 : mod_of T) (leq_of0 : leq_of T) (ts : seq (@task_T T)) 
  (Δ : T) =>
let work_ts :=
  [seq @task_rbf_T T zero_of0 one_of0 add_of0 mul_of0 div_of0 mod_of0 leq_of0 tsk' Δ | tsk' <- ts] in
@foldr T T +%C 0%C work_ts
     : forall {T : Type},
       zero_of T ->
       one_of T -> add_of T -> mul_of T -> div_of T -> mod_of T -> leq_of T -> seq (@task_T T) -> T -> T

Arguments total_rbf_T {T}%_type_scope {zero_of0 one_of0 add_of0 mul_of0 div_of0 mod_of0 leq_of0}
  ts%_seq_scope Δ
```

## Lean

```lean
@Prosa.Implementation.Refinements.EDF.Refinements.total_rbf_T : {T : Type} →
  [Prosa.Implementation.Refinements.Refinements.zero_of T] →
    [Prosa.Implementation.Refinements.Refinements.one_of T] →
      [Prosa.Implementation.Refinements.Refinements.add_of T] →
        [Prosa.Implementation.Refinements.Refinements.mul_of T] →
          [Prosa.Implementation.Refinements.Refinements.div_of T] →
            [Prosa.Implementation.Refinements.Refinements.mod_of T] →
              [Prosa.Implementation.Refinements.Refinements.leq_of T] →
                List (Prosa.Implementation.Refinements.Task.task_T T) → T → T
```

Body:

```lean
def Prosa.Implementation.Refinements.EDF.Refinements.total_rbf_T : {T : Type} →
  [Prosa.Implementation.Refinements.Refinements.zero_of T] →
    [Prosa.Implementation.Refinements.Refinements.one_of T] →
      [Prosa.Implementation.Refinements.Refinements.add_of T] →
        [Prosa.Implementation.Refinements.Refinements.mul_of T] →
          [Prosa.Implementation.Refinements.Refinements.div_of T] →
            [Prosa.Implementation.Refinements.Refinements.mod_of T] →
              [Prosa.Implementation.Refinements.Refinements.leq_of T] →
                List (Prosa.Implementation.Refinements.Task.task_T T) → T → T :=
fun {T} [Prosa.Implementation.Refinements.Refinements.zero_of T] [Prosa.Implementation.Refinements.Refinements.one_of T]
    [Prosa.Implementation.Refinements.Refinements.add_of T] [Prosa.Implementation.Refinements.Refinements.mul_of T]
    [Prosa.Implementation.Refinements.Refinements.div_of T] [Prosa.Implementation.Refinements.Refinements.mod_of T]
    [Prosa.Implementation.Refinements.Refinements.leq_of T] ts Δ =>
  have work_ts := List.map (fun tsk' => Prosa.Implementation.Refinements.Task.task_rbf_T tsk' Δ) ts;
  List.foldr Prosa.Implementation.Refinements.Refinements.add_op Prosa.Implementation.Refinements.Refinements.zero_op
    work_ts
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_EDF_Refinements_total_rbf_T
     : forall T : Type,
       Prosa_Implementation_Refinements_Refinements_zero_of T ->
       Prosa_Implementation_Refinements_Refinements_one_of T ->
       Prosa_Implementation_Refinements_Refinements_add_of T ->
       Prosa_Implementation_Refinements_Refinements_mul_of T ->
       Prosa_Implementation_Refinements_Refinements_div_of T ->
       Prosa_Implementation_Refinements_Refinements_mod_of T ->
       Prosa_Implementation_Refinements_Refinements_leq_of T ->
       List_inst1 (Prosa_Implementation_Refinements_Task_task_T T) -> T -> T
```

Body:

```coq
Prosa_Implementation_Refinements_EDF_Refinements_total_rbf_T@{} =
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
  (ts : List_inst1 (Prosa_Implementation_Refinements_Task_task_T T)) (_UU0394_ : T) =>
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
    ts
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
       List_inst1 (Prosa_Implementation_Refinements_Task_task_T T) -> T -> T

Arguments Prosa_Implementation_Refinements_EDF_Refinements_total_rbf_T T%_type_scope
  inst_3
  inst_6
  inst_9
  inst_12
  inst_15
  inst_18
  inst_21 
  ts _UU0394_
```
