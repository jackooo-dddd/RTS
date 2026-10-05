# `search_space_arrival_curve_prefix_FP`

- Kind (Rocq): Definition
- Rocq: `prosa.implementation.refinements.fast_search_space_computation.search_space_arrival_curve_prefix_FP`
- Lean: `Prosa.Implementation.Refinements.FastSearchSpaceComputation.search_space_arrival_curve_prefix_FP`
- Certificate: `search_space_arrival_curve_prefix_FP_correspondence`

## Official Rocq

```coq
search_space_arrival_curve_prefix_FP : Equality.sort Task -> nat -> seq nat

search_space_arrival_curve_prefix_FP is not universe polymorphic
Arguments search_space_arrival_curve_prefix_FP tsk L%_nat_scope
search_space_arrival_curve_prefix_FP is transparent
Expands to: Constant
            prosa.implementation.refinements.fast_search_space_computation.search_space_arrival_curve_prefix_FP
Declared in library prosa.implementation.refinements.fast_search_space_computation, line 33, characters 13-49
search_space_arrival_curve_prefix_FP
     : Equality.sort Task -> nat -> seq nat
```

Body:

```coq
search_space_arrival_curve_prefix_FP =
fun (tsk : Equality.sort Task) (L : nat) =>
let h := get_horizon_of_task tsk in
search_space_arrival_curve_prefix_FP_h (tsk : Equality.sort Task) 0 (L %/ h).+1
     : Equality.sort Task -> nat -> seq nat

Arguments search_space_arrival_curve_prefix_FP tsk L%_nat_scope
```

## Lean

```lean
Prosa.Implementation.Refinements.FastSearchSpaceComputation.search_space_arrival_curve_prefix_FP : Prosa.Implementation.Refinements.Task.Task →
  ℕ → List ℕ
```

Body:

```lean
def Prosa.Implementation.Refinements.FastSearchSpaceComputation.search_space_arrival_curve_prefix_FP : Prosa.Implementation.Refinements.Task.Task →
  ℕ → List ℕ :=
fun tsk L =>
  have h := Prosa.Implementation.Refinements.ArrivalCurve.get_horizon_of_task tsk;
  Prosa.Implementation.Refinements.FastSearchSpaceComputation.search_space_arrival_curve_prefix_FP_h tsk 0 (L / h + 1)
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_FastSearchSpaceComputation_search_space_arrival_curve_prefix_FP
     : Prosa_Implementation_Refinements_Task_Task -> Nat -> List_inst1 Nat
```

Body:

```coq
Prosa_Implementation_Refinements_FastSearchSpaceComputation_search_space_arrival_curve_prefix_FP@{} =
fun (tsk : Prosa_Implementation_Refinements_Task_Task) (L : Nat) =>
let h := Prosa_Implementation_Refinements_ArrivalCurve_get_horizon_of_task tsk in
Prosa_Implementation_Refinements_FastSearchSpaceComputation_search_space_arrival_curve_prefix_FP_h tsk
  (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0))
  (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat)
     (HDiv_hDiv_inst7 Nat Prosa_Behavior_Time_duration Nat (instHDiv_inst1 Nat Nat_instDiv) L h)
     (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1)))
     : Prosa_Implementation_Refinements_Task_Task -> Nat -> List_inst1 Nat

Arguments Prosa_Implementation_Refinements_FastSearchSpaceComputation_search_space_arrival_curve_prefix_FP
  tsk s%_Nat_scope
```
