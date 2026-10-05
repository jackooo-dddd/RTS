# `ohep_task_T`

- Kind (Rocq): Definition
- Rocq: `prosa.implementation.refinements.FP.refinements.ohep_task_T`
- Lean: `Prosa.Implementation.Refinements.FP.Refinements.ohep_task_T`
- Certificate: `ohep_task_T_correspondence`

## Official Rocq

```coq
ohep_task_T : forall {T : Type}, leq_of T -> eq_of (@task_T T) -> @task_T T -> @task_T T -> bool

ohep_task_T is not universe polymorphic
Arguments ohep_task_T {T}%_type_scope {leq_of0 eq_of2} tsk_o tsk
ohep_task_T is transparent
Expands to: Constant prosa.implementation.refinements.FP.refinements.ohep_task_T
Declared in library prosa.implementation.refinements.FP.refinements, line 30, characters 13-24
@ohep_task_T
     : forall T : Type, leq_of T -> eq_of (@task_T T) -> @task_T T -> @task_T T -> bool
```

Body:

```coq
ohep_task_T =
fun (T : Type) (leq_of0 : leq_of T) (eq_of2 : eq_of (@task_T T)) (tsk_o tsk : @task_T T) =>
@hep_task_T T leq_of0 tsk_o tsk && ~~ eq_of2 tsk_o tsk
     : forall {T : Type}, leq_of T -> eq_of (@task_T T) -> @task_T T -> @task_T T -> bool

Arguments ohep_task_T {T}%_type_scope {leq_of0 eq_of2} tsk_o tsk
```

## Lean

```lean
@Prosa.Implementation.Refinements.FP.Refinements.ohep_task_T : {T : Type} →
  [Prosa.Implementation.Refinements.Refinements.leq_of T] →
    [eq_of2 : Prosa.Implementation.Refinements.Refinements.eq_of (Prosa.Implementation.Refinements.Task.task_T T)] →
      Prosa.Implementation.Refinements.Task.task_T T → Prosa.Implementation.Refinements.Task.task_T T → Bool
```

Body:

```lean
def Prosa.Implementation.Refinements.FP.Refinements.ohep_task_T : {T : Type} →
  [Prosa.Implementation.Refinements.Refinements.leq_of T] →
    [eq_of2 : Prosa.Implementation.Refinements.Refinements.eq_of (Prosa.Implementation.Refinements.Task.task_T T)] →
      Prosa.Implementation.Refinements.Task.task_T T → Prosa.Implementation.Refinements.Task.task_T T → Bool :=
fun {T} [Prosa.Implementation.Refinements.Refinements.leq_of T]
    [Prosa.Implementation.Refinements.Refinements.eq_of (Prosa.Implementation.Refinements.Task.task_T T)] tsk_o tsk =>
  Prosa.Implementation.Refinements.FP.Refinements.hep_task_T tsk_o tsk &&
    !Prosa.Implementation.Refinements.Refinements.eq_op tsk_o tsk
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_FP_Refinements_ohep_task_T
     : forall T : Type,
       Prosa_Implementation_Refinements_Refinements_leq_of T ->
       Prosa_Implementation_Refinements_Refinements_eq_of (Prosa_Implementation_Refinements_Task_task_T T) ->
       Prosa_Implementation_Refinements_Task_task_T T ->
       Prosa_Implementation_Refinements_Task_task_T T -> Bool
```

Body:

```coq
Prosa_Implementation_Refinements_FP_Refinements_ohep_task_T@{} =
fun (T : Type)
  (inst_3 : 
   Prosa_Implementation_Refinements_Refinements_leq_of T)
  (eq_of2 : Prosa_Implementation_Refinements_Refinements_eq_of
              (Prosa_Implementation_Refinements_Task_task_T T))
  (tsk_o tsk : Prosa_Implementation_Refinements_Task_task_T T) =>
Bool_and
  (Prosa_Implementation_Refinements_FP_Refinements_hep_task_T T
     inst_3 tsk_o tsk)
  (Bool_not
     (Prosa_Implementation_Refinements_Refinements_eq_of_eq_op
        (Prosa_Implementation_Refinements_Task_task_T T) eq_of2 tsk_o tsk))
     : forall T : Type,
       Prosa_Implementation_Refinements_Refinements_leq_of T ->
       Prosa_Implementation_Refinements_Refinements_eq_of (Prosa_Implementation_Refinements_Task_task_T T) ->
       Prosa_Implementation_Refinements_Task_task_T T ->
       Prosa_Implementation_Refinements_Task_task_T T -> Bool

Arguments Prosa_Implementation_Refinements_FP_Refinements_ohep_task_T T%_type_scope
  inst_3 
  eq_of2 t1 t2
```
