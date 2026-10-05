# `search_space_emax_FP_h`

- Kind (Rocq): Definition
- Rocq: `prosa.implementation.refinements.FP.fast_search_space.search_space_emax_FP_h`
- Lean: `Prosa.Implementation.Refinements.FP.FastSearchSpace.search_space_emax_FP_h`
- Certificate: `search_space_emax_FP_h_correspondence`

## Official Rocq

```coq
search_space_emax_FP_h : Equality.sort Task -> nat -> nat -> seq nat

search_space_emax_FP_h is not universe polymorphic
Arguments search_space_emax_FP_h tsk (a b)%_nat_scope
search_space_emax_FP_h is transparent
Expands to: Constant prosa.implementation.refinements.FP.fast_search_space.search_space_emax_FP_h
Declared in library prosa.implementation.refinements.FP.fast_search_space, line 46, characters 11-33
search_space_emax_FP_h
     : Equality.sort Task -> nat -> nat -> seq nat
```

Body:

```coq
search_space_emax_FP_h =
fun (tsk : Equality.sort Task) (a b : nat) =>
let h := get_horizon_of_task tsk in
let offsets := [seq h * i | i <- iota a b] in
let emax_offsets := repeat_steps_with_offset tsk offsets in [seq i.-1 | i <- emax_offsets]
     : Equality.sort Task -> nat -> nat -> seq nat

Arguments search_space_emax_FP_h tsk (a b)%_nat_scope
```

## Lean

```lean
Prosa.Implementation.Refinements.FP.FastSearchSpace.search_space_emax_FP_h : Prosa.Implementation.Refinements.Task.Task →
  ℕ → ℕ → List ℕ
```

Body:

```lean
def Prosa.Implementation.Refinements.FP.FastSearchSpace.search_space_emax_FP_h : Prosa.Implementation.Refinements.Task.Task →
  ℕ → ℕ → List ℕ :=
fun tsk a b =>
  have h := Prosa.Implementation.Refinements.ArrivalCurve.get_horizon_of_task tsk;
  have offsets := List.map (fun x => h * x) (List.range' a b);
  have emax_offsets := Prosa.Implementation.Refinements.ArrivalCurve.repeat_steps_with_offset tsk offsets;
  List.map Nat.pred emax_offsets
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_FP_FastSearchSpace_search_space_emax_FP_h
     : Prosa_Implementation_Refinements_Task_Task -> Nat -> Nat -> List_inst1 Nat
```

Body:

```coq
Prosa_Implementation_Refinements_FP_FastSearchSpace_search_space_emax_FP_h@{} =
fun (tsk : Prosa_Implementation_Refinements_Task_Task) (l r : Nat) =>
let h := Prosa_Implementation_Refinements_ArrivalCurve_get_horizon_of_task tsk in
let offsets :=
  List_map_inst3 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
    (fun x : Prosa_Behavior_Time_duration =>
     HMul_hMul_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
       (instHMul_inst1 Prosa_Behavior_Time_duration instMulNat) h x)
    (List_range' l r (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1)))
  in
let arrival_curve_prefix_offsets :=
  Prosa_Implementation_Refinements_ArrivalCurve_repeat_steps_with_offset tsk offsets in
List_map_inst3 Nat Nat Nat_pred arrival_curve_prefix_offsets
     : Prosa_Implementation_Refinements_Task_Task -> Nat -> Nat -> List_inst1 Nat

Arguments Prosa_Implementation_Refinements_FP_FastSearchSpace_search_space_emax_FP_h 
  tsk (x____at___Init_Data_List_Basic527151790__hygCtx__hyg14 s)%_Nat_scope
```
