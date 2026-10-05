# `search_space_emax_FP`

- Kind (Rocq): Definition
- Rocq: `prosa.implementation.refinements.EDF.fast_search_space.search_space_emax_FP`
- Lean: `Prosa.Implementation.Refinements.EDF.FastSearchSpace.search_space_emax_FP`
- Certificate: `search_space_emax_FP_correspondence`

## Official Rocq

```coq
search_space_emax_FP : nat -> Equality.sort Task -> seq nat

search_space_emax_FP is not universe polymorphic
Arguments search_space_emax_FP L%_nat_scope tsk
search_space_emax_FP is transparent
Expands to: Constant prosa.implementation.refinements.EDF.fast_search_space.search_space_emax_FP
Declared in library prosa.implementation.refinements.EDF.fast_search_space, line 57, characters 13-33
search_space_emax_FP
     : nat -> Equality.sort Task -> seq nat
```

Body:

```coq
search_space_emax_FP =
fun (L : nat) (tsk : Equality.sort Task) =>
let h := get_horizon_of_task tsk in search_space_emax_FP_h (tsk : Equality.sort Task) 0 (L %/ h).+1
     : nat -> Equality.sort Task -> seq nat

Arguments search_space_emax_FP L%_nat_scope tsk
```

## Lean

```lean
Prosa.Implementation.Refinements.EDF.FastSearchSpace.search_space_emax_FP : ℕ →
  Prosa.Implementation.Refinements.EDF.FastSearchSpace.Task → List ℕ
```

Body:

```lean
def Prosa.Implementation.Refinements.EDF.FastSearchSpace.search_space_emax_FP : ℕ →
  Prosa.Implementation.Refinements.EDF.FastSearchSpace.Task → List ℕ :=
fun L tsk =>
  have h := Prosa.Implementation.Refinements.ArrivalCurve.get_horizon_of_task tsk;
  Prosa.Implementation.Refinements.EDF.FastSearchSpace.search_space_emax_FP_h tsk 0 (L / h + 1)
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_EDF_FastSearchSpace_search_space_emax_FP
     : Nat -> Prosa_Implementation_Refinements_EDF_FastSearchSpace_Task -> List_inst1 Nat
```

Body:

```coq
Prosa_Implementation_Refinements_EDF_FastSearchSpace_search_space_emax_FP@{} =
fun (L : Nat) (tsk : Prosa_Implementation_Refinements_EDF_FastSearchSpace_Task) =>
let h := Prosa_Implementation_Refinements_ArrivalCurve_get_horizon_of_task tsk in
Prosa_Implementation_Refinements_EDF_FastSearchSpace_search_space_emax_FP_h tsk
  (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0))
  (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat)
     (HDiv_hDiv_inst7 Nat Prosa_Behavior_Time_duration Nat (instHDiv_inst1 Nat Nat_instDiv) L h)
     (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1)))
     : Nat -> Prosa_Implementation_Refinements_EDF_FastSearchSpace_Task -> List_inst1 Nat

Arguments Prosa_Implementation_Refinements_EDF_FastSearchSpace_search_space_emax_FP L%_Nat_scope tsk
```
