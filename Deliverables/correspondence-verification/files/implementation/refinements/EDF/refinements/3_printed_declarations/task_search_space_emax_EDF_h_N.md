# `task_search_space_emax_EDF_h_N`

- Kind (Rocq): Definition
- Rocq: `prosa.implementation.refinements.EDF.refinements.task_search_space_emax_EDF_h_N`
- Lean: `Prosa.Implementation.Refinements.EDF.Refinements.task_search_space_emax_EDF_h_N`
- Certificate: `task_search_space_emax_EDF_h_N_correspondence`

## Official Rocq

```coq
task_search_space_emax_EDF_h_N : @task_T N -> @task_T N -> N -> N -> seq N

task_search_space_emax_EDF_h_N is not universe polymorphic
Arguments task_search_space_emax_EDF_h_N tsk tsko (l r)%_N_scope
task_search_space_emax_EDF_h_N is transparent
Expands to: Constant prosa.implementation.refinements.EDF.refinements.task_search_space_emax_EDF_h_N
Declared in library prosa.implementation.refinements.EDF.refinements, line 65, characters 11-41
task_search_space_emax_EDF_h_N
     : @task_T N -> @task_T N -> N -> N -> seq N
```

Body:

```coq
task_search_space_emax_EDF_h_N =
fun (tsk tsko : @task_T N) (l r : N) =>
let h := @get_horizon_of_task_T N one_N tsko in
let offsets := [seq (h * i)%num | i <- iota_N l r] in
let emax_offsets := @repeat_steps_with_offset_T N one_N add_N tsko offsets in
let emax_edf_offsets :=
  @shift_points_neg_T N sub_N leq_N (@shift_points_pos_T N add_N emax_offsets (@task_deadline_T N tsko))
    (@task_deadline_T N tsk)
  in
     : @task_T N -> @task_T N -> N -> N -> seq N

Arguments task_search_space_emax_EDF_h_N tsk tsko (l r)%_N_scope
```

## Lean

```lean
Prosa.Implementation.Refinements.EDF.Refinements.task_search_space_emax_EDF_h_N : Prosa.Implementation.Refinements.Task.task_T
    Prosa.Implementation.Refinements.Refinements.N →
  Prosa.Implementation.Refinements.Task.task_T Prosa.Implementation.Refinements.Refinements.N →
    Prosa.Implementation.Refinements.Refinements.N →
      Prosa.Implementation.Refinements.Refinements.N → List Prosa.Implementation.Refinements.Refinements.N
```

Body:

```lean
def Prosa.Implementation.Refinements.EDF.Refinements.task_search_space_emax_EDF_h_N : Prosa.Implementation.Refinements.Task.task_T
    Prosa.Implementation.Refinements.Refinements.N →
  Prosa.Implementation.Refinements.Task.task_T Prosa.Implementation.Refinements.Refinements.N →
    Prosa.Implementation.Refinements.Refinements.N →
      Prosa.Implementation.Refinements.Refinements.N → List Prosa.Implementation.Refinements.Refinements.N :=
fun tsk tsko l r =>
  have h := Prosa.Implementation.Refinements.Task.get_horizon_of_task_T tsko;
  have offsets := List.map (fun i => h.mul i) (Prosa.Implementation.Refinements.EDF.Refinements.iota_N l r);
  have emax_offsets := Prosa.Implementation.Refinements.Task.repeat_steps_with_offset_T tsko offsets;
  have emax_edf_offsets :=
    Prosa.Implementation.Refinements.Refinements.shift_points_neg_T
      (Prosa.Implementation.Refinements.Refinements.shift_points_pos_T emax_offsets tsko.task_deadline_T)
      tsk.task_deadline_T;
  List.map Prosa.Implementation.Refinements.Refinements.predn_T emax_edf_offsets
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_EDF_Refinements_task_search_space_emax_EDF_h_N
     : Prosa_Implementation_Refinements_Task_task_T Prosa_Implementation_Refinements_Refinements_N ->
       Prosa_Implementation_Refinements_Task_task_T Prosa_Implementation_Refinements_Refinements_N ->
       Prosa_Implementation_Refinements_Refinements_N ->
       Prosa_Implementation_Refinements_Refinements_N ->
       List_inst1 Prosa_Implementation_Refinements_Refinements_N
```

Body:

```coq
Prosa_Implementation_Refinements_EDF_Refinements_task_search_space_emax_EDF_h_N@{} =
fun (tsk tsko : Prosa_Implementation_Refinements_Task_task_T Prosa_Implementation_Refinements_Refinements_N)
  (l r : Prosa_Implementation_Refinements_Refinements_N) =>
let h :=
  Prosa_Implementation_Refinements_Task_get_horizon_of_task_T Prosa_Implementation_Refinements_Refinements_N
    Prosa_Implementation_Refinements_Refinements_one_N tsko
  in
let offsets :=
  List_map_inst3 Prosa_Implementation_Refinements_Refinements_N
    Prosa_Implementation_Refinements_Refinements_N
    (fun i : Prosa_Implementation_Refinements_Refinements_N =>
     Prosa_Implementation_Refinements_Refinements_N_mul h i)
    (Prosa_Implementation_Refinements_EDF_Refinements_iota_N l r)
  in
let emax_offsets :=
  Prosa_Implementation_Refinements_Task_repeat_steps_with_offset_T
    Prosa_Implementation_Refinements_Refinements_N Prosa_Implementation_Refinements_Refinements_one_N
    Prosa_Implementation_Refinements_Refinements_add_N tsko offsets
  in
let emax_edf_offsets :=
  Prosa_Implementation_Refinements_Refinements_shift_points_neg_T
    Prosa_Implementation_Refinements_Refinements_N Prosa_Implementation_Refinements_Refinements_sub_N
    Prosa_Implementation_Refinements_Refinements_leq_N
    (Prosa_Implementation_Refinements_Refinements_shift_points_pos_T
       Prosa_Implementation_Refinements_Refinements_N Prosa_Implementation_Refinements_Refinements_add_N
       emax_offsets
       (Prosa_Implementation_Refinements_Task_task_T_task_deadline_T
          Prosa_Implementation_Refinements_Refinements_N tsko))
    (Prosa_Implementation_Refinements_Task_task_T_task_deadline_T
       Prosa_Implementation_Refinements_Refinements_N tsk)
  in
List_map_inst3 Prosa_Implementation_Refinements_Refinements_N Prosa_Implementation_Refinements_Refinements_N
  (Prosa_Implementation_Refinements_Refinements_predn_T Prosa_Implementation_Refinements_Refinements_N
     Prosa_Implementation_Refinements_Refinements_one_N Prosa_Implementation_Refinements_Refinements_sub_N)
  emax_edf_offsets
     : Prosa_Implementation_Refinements_Task_task_T Prosa_Implementation_Refinements_Refinements_N ->
       Prosa_Implementation_Refinements_Task_task_T Prosa_Implementation_Refinements_Refinements_N ->
       Prosa_Implementation_Refinements_Refinements_N ->
       Prosa_Implementation_Refinements_Refinements_N ->
       List_inst1 Prosa_Implementation_Refinements_Refinements_N

Arguments Prosa_Implementation_Refinements_EDF_Refinements_task_search_space_emax_EDF_h_N tsk tsko a _UU0394_
```
