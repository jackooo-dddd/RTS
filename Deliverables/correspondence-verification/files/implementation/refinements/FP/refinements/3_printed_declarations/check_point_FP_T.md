# `check_point_FP_T`

- Kind (Rocq): Definition
- Rocq: `prosa.implementation.refinements.FP.refinements.check_point_FP_T`
- Lean: `Prosa.Implementation.Refinements.FP.Refinements.check_point_FP_T`
- Certificate: `check_point_FP_T_correspondence`

## Official Rocq

```coq
check_point_FP_T :
forall {T : Type},
zero_of T ->
one_of T ->
add_of T ->
mul_of T ->
div_of T -> mod_of T -> leq_of T -> eq_of (@task_T T) -> seq (@task_T T) -> @task_T T -> T -> T * T -> bool

check_point_FP_T is not universe polymorphic
Arguments check_point_FP_T {T}%_type_scope {zero_of0 one_of0 add_of0 mul_of0 div_of0 mod_of0 leq_of0 eq_of2}
  ts%_seq_scope tsk R P
check_point_FP_T is transparent
Expands to: Constant prosa.implementation.refinements.FP.refinements.check_point_FP_T
Declared in library prosa.implementation.refinements.FP.refinements, line 40, characters 13-29
@check_point_FP_T
     : forall T : Type,
       zero_of T ->
       one_of T ->
       add_of T ->
       mul_of T ->
       div_of T ->
       mod_of T -> leq_of T -> eq_of (@task_T T) -> seq (@task_T T) -> @task_T T -> T -> T * T -> bool
```

Body:

```coq
check_point_FP_T =
fun (T : Type) (zero_of0 : zero_of T) (one_of0 : one_of T) (add_of0 : add_of T) (mul_of0 : mul_of T)
  (div_of0 : div_of T) (mod_of0 : mod_of T) (leq_of0 : leq_of T) (eq_of2 : eq_of (@task_T T))
  (ts : seq (@task_T T)) (tsk : @task_T T) (R : T) (P : T * T) =>
(@task_rbf_T T zero_of0 one_of0 add_of0 mul_of0 div_of0 mod_of0 leq_of0 tsk (P.1 + 1) +
 @total_ohep_rbf_T T zero_of0 one_of0 add_of0 mul_of0 div_of0 mod_of0 leq_of0 eq_of2 ts tsk (P.1 + P.2) <=
 P.1 + P.2)%C &&
(P.2 <= R)%C
     : forall {T : Type},
       zero_of T ->
       one_of T ->
       add_of T ->
       mul_of T ->
       div_of T ->
       mod_of T -> leq_of T -> eq_of (@task_T T) -> seq (@task_T T) -> @task_T T -> T -> T * T -> bool

Arguments check_point_FP_T {T}%_type_scope {zero_of0 one_of0 add_of0 mul_of0 div_of0 mod_of0 leq_of0 eq_of2}
  ts%_seq_scope tsk R P
```

## Lean

```lean
@Prosa.Implementation.Refinements.FP.Refinements.check_point_FP_T : {T : Type} →
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
                    Prosa.Implementation.Refinements.Task.task_T T → T → T × T → Bool
```

Body:

```lean
def Prosa.Implementation.Refinements.FP.Refinements.check_point_FP_T : {T : Type} →
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
                    Prosa.Implementation.Refinements.Task.task_T T → T → T × T → Bool :=
fun {T} [Prosa.Implementation.Refinements.Refinements.zero_of T] [Prosa.Implementation.Refinements.Refinements.one_of T]
    [Prosa.Implementation.Refinements.Refinements.add_of T] [Prosa.Implementation.Refinements.Refinements.mul_of T]
    [Prosa.Implementation.Refinements.Refinements.div_of T] [Prosa.Implementation.Refinements.Refinements.mod_of T]
    [Prosa.Implementation.Refinements.Refinements.leq_of T]
    [Prosa.Implementation.Refinements.Refinements.eq_of (Prosa.Implementation.Refinements.Task.task_T T)] ts tsk R P =>
  Prosa.Implementation.Refinements.Refinements.leq_op
      (Prosa.Implementation.Refinements.Refinements.add_op
        (Prosa.Implementation.Refinements.Task.task_rbf_T tsk
          (Prosa.Implementation.Refinements.Refinements.add_op P.1 Prosa.Implementation.Refinements.Refinements.one_op))
        (Prosa.Implementation.Refinements.FP.Refinements.total_ohep_rbf_T ts tsk
          (Prosa.Implementation.Refinements.Refinements.add_op P.1 P.2)))
      (Prosa.Implementation.Refinements.Refinements.add_op P.1 P.2) &&
    Prosa.Implementation.Refinements.Refinements.leq_op P.2 R
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_FP_Refinements_check_point_FP_T
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
       Prosa_Implementation_Refinements_Task_task_T T -> T -> Prod_inst3 T T -> Bool
```

Body:

```coq
Prosa_Implementation_Refinements_FP_Refinements_check_point_FP_T@{} =
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
  (tsk : Prosa_Implementation_Refinements_Task_task_T T) (R : T) (P : Prod_inst3 T T) =>
Bool_and
  (Prosa_Implementation_Refinements_Refinements_leq_of_leq_op T
     inst_21
     (Prosa_Implementation_Refinements_Refinements_add_of_add_op T
        inst_9
        (Prosa_Implementation_Refinements_Task_task_rbf_T T
           inst_3
           inst_6
           inst_9
           inst_12
           inst_15
           inst_18
           inst_21 tsk
           (Prosa_Implementation_Refinements_Refinements_add_of_add_op T
              inst_9
              (Prod_fst_inst3 T T P)
              (Prosa_Implementation_Refinements_Refinements_one_of_one_op T
                 inst_6)))
        (Prosa_Implementation_Refinements_FP_Refinements_total_ohep_rbf_T T
           inst_3
           inst_6
           inst_9
           inst_12
           inst_15
           inst_18
           inst_21 eq_of2 ts
           tsk
           (Prosa_Implementation_Refinements_Refinements_add_of_add_op T
              inst_9
              (Prod_fst_inst3 T T P) (Prod_snd_inst3 T T P))))
     (Prosa_Implementation_Refinements_Refinements_add_of_add_op T
        inst_9
        (Prod_fst_inst3 T T P) (Prod_snd_inst3 T T P)))
  (Prosa_Implementation_Refinements_Refinements_leq_of_leq_op T
     inst_21
     (Prod_snd_inst3 T T P) R)
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
       Prosa_Implementation_Refinements_Task_task_T T -> T -> Prod_inst3 T T -> Bool

Arguments Prosa_Implementation_Refinements_FP_Refinements_check_point_FP_T T%_type_scope
  inst_3
  inst_6
  inst_9
  inst_12
  inst_15
  inst_18
  inst_21 
  eq_of2 ts tsk R P
```
