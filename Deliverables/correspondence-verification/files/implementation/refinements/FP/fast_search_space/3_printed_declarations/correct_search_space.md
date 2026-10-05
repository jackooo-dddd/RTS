# `correct_search_space`

- Kind (Rocq): Definition
- Rocq: `prosa.implementation.refinements.FP.fast_search_space.correct_search_space`
- Lean: `Prosa.Implementation.Refinements.FP.FastSearchSpace.correct_search_space`
- Certificate: `correct_search_space_correspondence`

## Official Rocq

```coq
correct_search_space : Equality.sort Task -> duration -> seq nat

correct_search_space is not universe polymorphic
Arguments correct_search_space tsk L
correct_search_space is transparent
Expands to: Constant prosa.implementation.refinements.FP.fast_search_space.correct_search_space
Declared in library prosa.implementation.refinements.FP.fast_search_space, line 41, characters 11-31
correct_search_space
     : Equality.sort Task -> duration -> seq nat
```

Body:

```coq
correct_search_space =
fun (tsk : Equality.sort Task) (L : duration) =>
     : Equality.sort Task -> duration -> seq nat

Arguments correct_search_space tsk L
```

## Lean

```lean
Prosa.Implementation.Refinements.FP.FastSearchSpace.correct_search_space : Prosa.Implementation.Refinements.Task.Task →
  Prosa.Behavior.Time.duration → List ℕ
```

Body:

```lean
def Prosa.Implementation.Refinements.FP.FastSearchSpace.correct_search_space : Prosa.Implementation.Refinements.Task.Task →
  Prosa.Behavior.Time.duration → List ℕ :=
fun tsk L => List.filter (fun A => Prosa.Results.Rta.Ideal.Fp.BoundedPi.is_in_search_space tsk L A) (List.range' 0 L)
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_FP_FastSearchSpace_correct_search_space
     : Prosa_Implementation_Refinements_Task_Task -> Prosa_Behavior_Time_duration -> List_inst1 Nat
```

Body:

```coq
Prosa_Implementation_Refinements_FP_FastSearchSpace_correct_search_space@{} =
fun (tsk : Prosa_Implementation_Refinements_Task_Task) (L : Prosa_Behavior_Time_duration) =>
List_filter_inst1 Nat
  (fun A : Nat =>
   Prosa_Results_Rta_Ideal_Fp_BoundedPi_is_in_search_space_inst1 Prosa_Implementation_Refinements_Task_Task
     Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_task
     Prosa_Implementation_Definitions_Task_TaskCost Prosa_Implementation_Definitions_Task_ConcreteMaxArrivals
     tsk L A)
  (List_range' (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0)) L (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1)))
     : Prosa_Implementation_Refinements_Task_Task -> Prosa_Behavior_Time_duration -> List_inst1 Nat

Arguments Prosa_Implementation_Refinements_FP_FastSearchSpace_correct_search_space tsk L
```
