# `search_space_emax_FP_h_N`

- Kind (Rocq): Definition
- Rocq: `prosa.implementation.refinements.FP.refinements.search_space_emax_FP_h_N`
- Lean: `Prosa.Implementation.Refinements.FP.Refinements.search_space_emax_FP_h_N`
- Certificate: `search_space_emax_FP_h_N_correspondence`

## Official Rocq

```coq
search_space_emax_FP_h_N : @task_T N -> N -> N -> seq N

search_space_emax_FP_h_N is not universe polymorphic
Arguments search_space_emax_FP_h_N tsk (l r)%_N_scope
search_space_emax_FP_h_N is transparent
Expands to: Constant prosa.implementation.refinements.FP.refinements.search_space_emax_FP_h_N
Declared in library prosa.implementation.refinements.FP.refinements, line 65, characters 11-35
search_space_emax_FP_h_N
     : @task_T N -> N -> N -> seq N
```

Body:

```coq
search_space_emax_FP_h_N =
fun (tsk : @task_T N) (l r : N) =>
let h := @get_horizon_of_task_T N one_N tsk in
let offsets := [seq (h * i)%num | i <- iota_N l r] in
let emax_offsets := @repeat_steps_with_offset_T N one_N add_N tsk offsets in
     : @task_T N -> N -> N -> seq N

Arguments search_space_emax_FP_h_N tsk (l r)%_N_scope
```

## Lean

```lean
Prosa.Implementation.Refinements.FP.Refinements.search_space_emax_FP_h_N : Prosa.Implementation.Refinements.Task.task_T
    Prosa.Implementation.Refinements.Refinements.N →
  Prosa.Implementation.Refinements.Refinements.N →
    Prosa.Implementation.Refinements.Refinements.N → List Prosa.Implementation.Refinements.Refinements.N
```

Body:

```lean
def Prosa.Implementation.Refinements.FP.Refinements.search_space_emax_FP_h_N : Prosa.Implementation.Refinements.Task.task_T
    Prosa.Implementation.Refinements.Refinements.N →
  Prosa.Implementation.Refinements.Refinements.N →
    Prosa.Implementation.Refinements.Refinements.N → List Prosa.Implementation.Refinements.Refinements.N :=
fun tsk l r =>
  have h := Prosa.Implementation.Refinements.Task.get_horizon_of_task_T tsk;
  have offsets := List.map (fun i => h.mul i) (Prosa.Implementation.Refinements.FP.Refinements.iota_N l r);
  have emax_offsets := Prosa.Implementation.Refinements.Task.repeat_steps_with_offset_T tsk offsets;
  List.map Prosa.Implementation.Refinements.Refinements.predn_T emax_offsets
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_FP_Refinements_search_space_emax_FP_h_N
     : Prosa_Implementation_Refinements_Task_task_T Prosa_Implementation_Refinements_Refinements_N ->
       Prosa_Implementation_Refinements_Refinements_N ->
       Prosa_Implementation_Refinements_Refinements_N ->
       List_inst1 Prosa_Implementation_Refinements_Refinements_N
```

Body:

```coq
Prosa_Implementation_Refinements_FP_Refinements_search_space_emax_FP_h_N@{} =
fun (tsk : Prosa_Implementation_Refinements_Task_task_T Prosa_Implementation_Refinements_Refinements_N)
  (l r : Prosa_Implementation_Refinements_Refinements_N) =>
let h :=
  Prosa_Implementation_Refinements_Task_get_horizon_of_task_T Prosa_Implementation_Refinements_Refinements_N
    Prosa_Implementation_Refinements_Refinements_one_N tsk
  in
let offsets :=
  List_map_inst3 Prosa_Implementation_Refinements_Refinements_N
    Prosa_Implementation_Refinements_Refinements_N
    (fun i : Prosa_Implementation_Refinements_Refinements_N =>
     Prosa_Implementation_Refinements_Refinements_N_mul h i)
    (Prosa_Implementation_Refinements_FP_Refinements_iota_N l r)
  in
let emax_offsets :=
  Prosa_Implementation_Refinements_Task_repeat_steps_with_offset_T
    Prosa_Implementation_Refinements_Refinements_N Prosa_Implementation_Refinements_Refinements_one_N
    Prosa_Implementation_Refinements_Refinements_add_N tsk offsets
  in
List_map_inst3 Prosa_Implementation_Refinements_Refinements_N Prosa_Implementation_Refinements_Refinements_N
  (Prosa_Implementation_Refinements_Refinements_predn_T Prosa_Implementation_Refinements_Refinements_N
     Prosa_Implementation_Refinements_Refinements_one_N Prosa_Implementation_Refinements_Refinements_sub_N)
  emax_offsets
     : Prosa_Implementation_Refinements_Task_task_T Prosa_Implementation_Refinements_Refinements_N ->
       Prosa_Implementation_Refinements_Refinements_N ->
       Prosa_Implementation_Refinements_Refinements_N ->
       List_inst1 Prosa_Implementation_Refinements_Refinements_N

Arguments Prosa_Implementation_Refinements_FP_Refinements_search_space_emax_FP_h_N tsk a _UU0394_
```
