# `task_search_space_emax_EDF_N`

- Kind (Rocq): Definition
- Rocq: `prosa.implementation.refinements.EDF.refinements.task_search_space_emax_EDF_N`
- Lean: `Prosa.Implementation.Refinements.EDF.Refinements.task_search_space_emax_EDF_N`
- Certificate: `task_search_space_emax_EDF_N_correspondence`

## Official Rocq

```coq
task_search_space_emax_EDF_N : @task_T N -> @task_T N -> N -> seq N

task_search_space_emax_EDF_N is not universe polymorphic
Arguments task_search_space_emax_EDF_N tsk tsko L%_N_scope
task_search_space_emax_EDF_N is transparent
Expands to: Constant prosa.implementation.refinements.EDF.refinements.task_search_space_emax_EDF_N
Declared in library prosa.implementation.refinements.EDF.refinements, line 76, characters 11-39
task_search_space_emax_EDF_N
     : @task_T N -> @task_T N -> N -> seq N
```

Body:

```coq
task_search_space_emax_EDF_N =
fun (tsk tsko : @task_T N) (L : N) =>
let h := @get_horizon_of_task_T N one_N tsko in
task_search_space_emax_EDF_h_N tsk tsko 0
  ((L + (@task_deadline_T N tsk - @task_deadline_T N tsko)) %/ h + 1)%C
     : @task_T N -> @task_T N -> N -> seq N

Arguments task_search_space_emax_EDF_N tsk tsko L%_N_scope
```

## Lean

```lean
Prosa.Implementation.Refinements.EDF.Refinements.task_search_space_emax_EDF_N : Prosa.Implementation.Refinements.Task.task_T
    Prosa.Implementation.Refinements.Refinements.N →
  Prosa.Implementation.Refinements.Task.task_T Prosa.Implementation.Refinements.Refinements.N →
    Prosa.Implementation.Refinements.Refinements.N → List Prosa.Implementation.Refinements.Refinements.N
```

Body:

```lean
def Prosa.Implementation.Refinements.EDF.Refinements.task_search_space_emax_EDF_N : Prosa.Implementation.Refinements.Task.task_T
    Prosa.Implementation.Refinements.Refinements.N →
  Prosa.Implementation.Refinements.Task.task_T Prosa.Implementation.Refinements.Refinements.N →
    Prosa.Implementation.Refinements.Refinements.N → List Prosa.Implementation.Refinements.Refinements.N :=
fun tsk tsko L =>
  have h := Prosa.Implementation.Refinements.Task.get_horizon_of_task_T tsko;
  Prosa.Implementation.Refinements.EDF.Refinements.task_search_space_emax_EDF_h_N tsk tsko
    Prosa.Implementation.Refinements.Refinements.N.N0
    (Prosa.Implementation.Refinements.Refinements.add_op
      (Prosa.Implementation.Refinements.Refinements.div_op
        (Prosa.Implementation.Refinements.Refinements.add_op L
          (Prosa.Implementation.Refinements.Refinements.sub_op tsk.task_deadline_T tsko.task_deadline_T))
        h)
      Prosa.Implementation.Refinements.Refinements.one_op)
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_EDF_Refinements_task_search_space_emax_EDF_N
     : Prosa_Implementation_Refinements_Task_task_T Prosa_Implementation_Refinements_Refinements_N ->
       Prosa_Implementation_Refinements_Task_task_T Prosa_Implementation_Refinements_Refinements_N ->
       Prosa_Implementation_Refinements_Refinements_N ->
       List_inst1 Prosa_Implementation_Refinements_Refinements_N
```

Body:

```coq
Prosa_Implementation_Refinements_EDF_Refinements_task_search_space_emax_EDF_N@{} =
fun (tsk tsko : Prosa_Implementation_Refinements_Task_task_T Prosa_Implementation_Refinements_Refinements_N)
  (L : Prosa_Implementation_Refinements_Refinements_N) =>
let h :=
  Prosa_Implementation_Refinements_Task_get_horizon_of_task_T Prosa_Implementation_Refinements_Refinements_N
    Prosa_Implementation_Refinements_Refinements_one_N tsko
  in
Prosa_Implementation_Refinements_EDF_Refinements_task_search_space_emax_EDF_h_N tsk tsko
  Prosa_Implementation_Refinements_Refinements_N_N0
  (Prosa_Implementation_Refinements_Refinements_add_of_add_op Prosa_Implementation_Refinements_Refinements_N
     Prosa_Implementation_Refinements_Refinements_add_N
     (Prosa_Implementation_Refinements_Refinements_div_of_div_op
        Prosa_Implementation_Refinements_Refinements_N Prosa_Implementation_Refinements_Refinements_div_N
        (Prosa_Implementation_Refinements_Refinements_add_of_add_op
           Prosa_Implementation_Refinements_Refinements_N Prosa_Implementation_Refinements_Refinements_add_N
           L
           (Prosa_Implementation_Refinements_Refinements_sub_of_sub_op
              Prosa_Implementation_Refinements_Refinements_N
              Prosa_Implementation_Refinements_Refinements_sub_N
              (Prosa_Implementation_Refinements_Task_task_T_task_deadline_T
                 Prosa_Implementation_Refinements_Refinements_N tsk)
              (Prosa_Implementation_Refinements_Task_task_T_task_deadline_T
                 Prosa_Implementation_Refinements_Refinements_N tsko)))
        h)
     (Prosa_Implementation_Refinements_Refinements_one_of_one_op
        Prosa_Implementation_Refinements_Refinements_N Prosa_Implementation_Refinements_Refinements_one_N))
     : Prosa_Implementation_Refinements_Task_task_T Prosa_Implementation_Refinements_Refinements_N ->
       Prosa_Implementation_Refinements_Task_task_T Prosa_Implementation_Refinements_Refinements_N ->
       Prosa_Implementation_Refinements_Refinements_N ->
       List_inst1 Prosa_Implementation_Refinements_Refinements_N

Arguments Prosa_Implementation_Refinements_EDF_Refinements_task_search_space_emax_EDF_N tsk tsko _UU0394_
```
