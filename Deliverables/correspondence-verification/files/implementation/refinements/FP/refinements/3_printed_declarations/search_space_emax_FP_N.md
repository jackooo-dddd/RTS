# `search_space_emax_FP_N`

- Kind (Rocq): Definition
- Rocq: `prosa.implementation.refinements.FP.refinements.search_space_emax_FP_N`
- Lean: `Prosa.Implementation.Refinements.FP.Refinements.search_space_emax_FP_N`
- Certificate: `search_space_emax_FP_N_correspondence`

## Official Rocq

```coq
search_space_emax_FP_N : @task_T N -> N -> seq N

search_space_emax_FP_N is not universe polymorphic
Arguments search_space_emax_FP_N tsk L%_N_scope
search_space_emax_FP_N is transparent
Expands to: Constant prosa.implementation.refinements.FP.refinements.search_space_emax_FP_N
Declared in library prosa.implementation.refinements.FP.refinements, line 72, characters 11-33
search_space_emax_FP_N
     : @task_T N -> N -> seq N
```

Body:

```coq
search_space_emax_FP_N =
fun (tsk : @task_T N) (L : N) =>
let h := @get_horizon_of_task_T N one_N tsk in search_space_emax_FP_h_N tsk 0 (L %/ h + 1)%C
     : @task_T N -> N -> seq N

Arguments search_space_emax_FP_N tsk L%_N_scope
```

## Lean

```lean
Prosa.Implementation.Refinements.FP.Refinements.search_space_emax_FP_N : Prosa.Implementation.Refinements.Task.task_T
    Prosa.Implementation.Refinements.Refinements.N →
  Prosa.Implementation.Refinements.Refinements.N → List Prosa.Implementation.Refinements.Refinements.N
```

Body:

```lean
def Prosa.Implementation.Refinements.FP.Refinements.search_space_emax_FP_N : Prosa.Implementation.Refinements.Task.task_T
    Prosa.Implementation.Refinements.Refinements.N →
  Prosa.Implementation.Refinements.Refinements.N → List Prosa.Implementation.Refinements.Refinements.N :=
fun tsk L =>
  have h := Prosa.Implementation.Refinements.Task.get_horizon_of_task_T tsk;
  Prosa.Implementation.Refinements.FP.Refinements.search_space_emax_FP_h_N tsk
    Prosa.Implementation.Refinements.Refinements.N.N0
    (Prosa.Implementation.Refinements.Refinements.add_op (Prosa.Implementation.Refinements.Refinements.div_op L h)
      Prosa.Implementation.Refinements.Refinements.one_op)
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_FP_Refinements_search_space_emax_FP_N
     : Prosa_Implementation_Refinements_Task_task_T Prosa_Implementation_Refinements_Refinements_N ->
       Prosa_Implementation_Refinements_Refinements_N ->
       List_inst1 Prosa_Implementation_Refinements_Refinements_N
```

Body:

```coq
Prosa_Implementation_Refinements_FP_Refinements_search_space_emax_FP_N@{} =
fun (tsk : Prosa_Implementation_Refinements_Task_task_T Prosa_Implementation_Refinements_Refinements_N)
  (L : Prosa_Implementation_Refinements_Refinements_N) =>
let h :=
  Prosa_Implementation_Refinements_Task_get_horizon_of_task_T Prosa_Implementation_Refinements_Refinements_N
    Prosa_Implementation_Refinements_Refinements_one_N tsk
  in
Prosa_Implementation_Refinements_FP_Refinements_search_space_emax_FP_h_N tsk
  Prosa_Implementation_Refinements_Refinements_N_N0
  (Prosa_Implementation_Refinements_Refinements_add_of_add_op Prosa_Implementation_Refinements_Refinements_N
     Prosa_Implementation_Refinements_Refinements_add_N
     (Prosa_Implementation_Refinements_Refinements_div_of_div_op
        Prosa_Implementation_Refinements_Refinements_N Prosa_Implementation_Refinements_Refinements_div_N L h)
     (Prosa_Implementation_Refinements_Refinements_one_of_one_op
        Prosa_Implementation_Refinements_Refinements_N Prosa_Implementation_Refinements_Refinements_one_N))
     : Prosa_Implementation_Refinements_Task_task_T Prosa_Implementation_Refinements_Refinements_N ->
       Prosa_Implementation_Refinements_Refinements_N ->
       List_inst1 Prosa_Implementation_Refinements_Refinements_N

Arguments Prosa_Implementation_Refinements_FP_Refinements_search_space_emax_FP_N tsk _UU0394_
```
