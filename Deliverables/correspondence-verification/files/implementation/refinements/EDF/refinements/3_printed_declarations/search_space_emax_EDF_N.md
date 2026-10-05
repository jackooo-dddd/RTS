# `search_space_emax_EDF_N`

- Kind (Rocq): Definition
- Rocq: `prosa.implementation.refinements.EDF.refinements.search_space_emax_EDF_N`
- Lean: `Prosa.Implementation.Refinements.EDF.Refinements.search_space_emax_EDF_N`
- Certificate: `search_space_emax_EDF_N_correspondence`

## Official Rocq

```coq
search_space_emax_EDF_N : seq (@task_T N) -> @task_T N -> N -> seq N

search_space_emax_EDF_N is not universe polymorphic
Arguments search_space_emax_EDF_N ts%_seq_scope tsk L%_N_scope
search_space_emax_EDF_N is transparent
Expands to: Constant prosa.implementation.refinements.EDF.refinements.search_space_emax_EDF_N
Declared in library prosa.implementation.refinements.EDF.refinements, line 83, characters 11-34
search_space_emax_EDF_N
     : seq (@task_T N) -> @task_T N -> N -> seq N
```

Body:

```coq
search_space_emax_EDF_N =
fun (ts : seq (@task_T N)) (tsk : @task_T N) (L : N) =>
let points := [seq task_search_space_emax_EDF_N tsk tsko L | tsko <- ts] in @flatten N points
     : seq (@task_T N) -> @task_T N -> N -> seq N

Arguments search_space_emax_EDF_N ts%_seq_scope tsk L%_N_scope
```

## Lean

```lean
Prosa.Implementation.Refinements.EDF.Refinements.search_space_emax_EDF_N : List
    (Prosa.Implementation.Refinements.Task.task_T Prosa.Implementation.Refinements.Refinements.N) →
  Prosa.Implementation.Refinements.Task.task_T Prosa.Implementation.Refinements.Refinements.N →
    Prosa.Implementation.Refinements.Refinements.N → List Prosa.Implementation.Refinements.Refinements.N
```

Body:

```lean
def Prosa.Implementation.Refinements.EDF.Refinements.search_space_emax_EDF_N : List
    (Prosa.Implementation.Refinements.Task.task_T Prosa.Implementation.Refinements.Refinements.N) →
  Prosa.Implementation.Refinements.Task.task_T Prosa.Implementation.Refinements.Refinements.N →
    Prosa.Implementation.Refinements.Refinements.N → List Prosa.Implementation.Refinements.Refinements.N :=
fun ts tsk L =>
  have points :=
    List.map (fun tsko => Prosa.Implementation.Refinements.EDF.Refinements.task_search_space_emax_EDF_N tsk tsko L) ts;
  points.flatten
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_EDF_Refinements_search_space_emax_EDF_N
     : List_inst1
         (Prosa_Implementation_Refinements_Task_task_T Prosa_Implementation_Refinements_Refinements_N) ->
       Prosa_Implementation_Refinements_Task_task_T Prosa_Implementation_Refinements_Refinements_N ->
       Prosa_Implementation_Refinements_Refinements_N ->
       List_inst1 Prosa_Implementation_Refinements_Refinements_N
```

Body:

```coq
Prosa_Implementation_Refinements_EDF_Refinements_search_space_emax_EDF_N@{} =
fun
  (ts : List_inst1
          (Prosa_Implementation_Refinements_Task_task_T Prosa_Implementation_Refinements_Refinements_N))
  (tsk : Prosa_Implementation_Refinements_Task_task_T Prosa_Implementation_Refinements_Refinements_N)
  (L : Prosa_Implementation_Refinements_Refinements_N) =>
let points :=
  List_map_inst3
    (Prosa_Implementation_Refinements_Task_task_T Prosa_Implementation_Refinements_Refinements_N)
    (List_inst1 Prosa_Implementation_Refinements_Refinements_N)
    (fun tsko : Prosa_Implementation_Refinements_Task_task_T Prosa_Implementation_Refinements_Refinements_N =>
     Prosa_Implementation_Refinements_EDF_Refinements_task_search_space_emax_EDF_N tsk tsko L)
    ts
  in
List_flatten_inst1 Prosa_Implementation_Refinements_Refinements_N points
     : List_inst1
         (Prosa_Implementation_Refinements_Task_task_T Prosa_Implementation_Refinements_Refinements_N) ->
       Prosa_Implementation_Refinements_Task_task_T Prosa_Implementation_Refinements_Refinements_N ->
       Prosa_Implementation_Refinements_Refinements_N ->
       List_inst1 Prosa_Implementation_Refinements_Refinements_N

Arguments Prosa_Implementation_Refinements_EDF_Refinements_search_space_emax_EDF_N ts tsko _UU0394_
```
