# `search_space_emax_FP`

- Kind (Rocq): Definition
- Rocq: `prosa.implementation.refinements.FP.fast_search_space.search_space_emax_FP`
- Lean: `Prosa.Implementation.Refinements.FP.FastSearchSpace.search_space_emax_FP`
- Certificate: `search_space_emax_FP_correspondence`

## Official Rocq

```coq
search_space_emax_FP : Equality.sort Task -> duration -> seq nat

search_space_emax_FP is not universe polymorphic
Arguments search_space_emax_FP tsk L
search_space_emax_FP is transparent
Expands to: Constant prosa.implementation.refinements.FP.fast_search_space.search_space_emax_FP
Declared in library prosa.implementation.refinements.FP.fast_search_space, line 53, characters 11-31
search_space_emax_FP
     : Equality.sort Task -> duration -> seq nat
```

Body:

```coq
search_space_emax_FP =
fun (tsk : Equality.sort Task) (L : duration) =>
let h := get_horizon_of_task tsk in search_space_emax_FP_h tsk 0 (L %/ h).+1
     : Equality.sort Task -> duration -> seq nat

Arguments search_space_emax_FP tsk L
```

## Lean

```lean
Prosa.Implementation.Refinements.FP.FastSearchSpace.search_space_emax_FP : Prosa.Implementation.Refinements.Task.Task →
  Prosa.Behavior.Time.duration → List ℕ
```

Body:

```lean
def Prosa.Implementation.Refinements.FP.FastSearchSpace.search_space_emax_FP : Prosa.Implementation.Refinements.Task.Task →
  Prosa.Behavior.Time.duration → List ℕ :=
fun tsk L =>
  have h := Prosa.Implementation.Refinements.ArrivalCurve.get_horizon_of_task tsk;
  Prosa.Implementation.Refinements.FP.FastSearchSpace.search_space_emax_FP_h tsk 0 (L / h + 1)
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_FP_FastSearchSpace_search_space_emax_FP
     : Prosa_Implementation_Refinements_Task_Task -> Prosa_Behavior_Time_duration -> List_inst1 Nat
```

Body:

```coq
Prosa_Implementation_Refinements_FP_FastSearchSpace_search_space_emax_FP@{} =
fun (tsk : Prosa_Implementation_Refinements_Task_Task) (L : Prosa_Behavior_Time_duration) =>
let h := Prosa_Implementation_Refinements_ArrivalCurve_get_horizon_of_task tsk in
Prosa_Implementation_Refinements_FP_FastSearchSpace_search_space_emax_FP_h tsk
  (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0))
  (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Nat Prosa_Behavior_Time_duration
     (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat)
     (HDiv_hDiv_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
        (instHDiv_inst1 Prosa_Behavior_Time_duration Nat_instDiv) L h)
     (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1)))
     : Prosa_Implementation_Refinements_Task_Task -> Prosa_Behavior_Time_duration -> List_inst1 Nat

Arguments Prosa_Implementation_Refinements_FP_FastSearchSpace_search_space_emax_FP tsk L
```
