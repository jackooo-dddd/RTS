# `correct_search_space`

- Kind (Rocq): Definition
- Rocq: `prosa.implementation.refinements.EDF.fast_search_space.correct_search_space`
- Lean: `Prosa.Implementation.Refinements.EDF.FastSearchSpace.correct_search_space`
- Certificate: `correct_search_space_correspondence`

## Official Rocq

```coq
correct_search_space : seq (Equality.sort Task) -> Equality.sort Task -> duration -> seq duration

correct_search_space is not universe polymorphic
Arguments correct_search_space ts%_seq_scope tsk L
correct_search_space is transparent
Expands to: Constant prosa.implementation.refinements.EDF.fast_search_space.correct_search_space
Declared in library prosa.implementation.refinements.EDF.fast_search_space, line 43, characters 13-33
correct_search_space
     : seq (Equality.sort Task) -> Equality.sort Task -> duration -> seq duration
```

Body:

```coq
correct_search_space =
fun (ts : seq (Equality.sort Task)) (tsk : Equality.sort Task) (L : duration) =>
     : seq (Equality.sort Task) -> Equality.sort Task -> duration -> seq duration

Arguments correct_search_space ts%_seq_scope tsk L
```

## Lean

```lean
Prosa.Implementation.Refinements.EDF.FastSearchSpace.correct_search_space : List
    Prosa.Implementation.Refinements.EDF.FastSearchSpace.Task →
  Prosa.Implementation.Refinements.EDF.FastSearchSpace.Task →
    Prosa.Behavior.Time.duration → List Prosa.Behavior.Time.duration
```

Body:

```lean
def Prosa.Implementation.Refinements.EDF.FastSearchSpace.correct_search_space : List
    Prosa.Implementation.Refinements.EDF.FastSearchSpace.Task →
  Prosa.Implementation.Refinements.EDF.FastSearchSpace.Task →
    Prosa.Behavior.Time.duration → List Prosa.Behavior.Time.duration :=
fun ts tsk L =>
  List.filter (fun A => Prosa.Results.Rta.Ideal.Edf.BoundedNps.is_in_search_space ts tsk L A) (List.range' 0 L)
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_EDF_FastSearchSpace_correct_search_space
     : List_inst1 Prosa_Implementation_Refinements_EDF_FastSearchSpace_Task ->
       Prosa_Implementation_Refinements_EDF_FastSearchSpace_Task ->
       Prosa_Behavior_Time_duration -> List_inst1 Prosa_Behavior_Time_duration
```

Body:

```coq
Prosa_Implementation_Refinements_EDF_FastSearchSpace_correct_search_space@{} =
fun (ts : List_inst1 Prosa_Implementation_Refinements_EDF_FastSearchSpace_Task)
  (tsk : Prosa_Implementation_Refinements_EDF_FastSearchSpace_Task) (L : Prosa_Behavior_Time_duration) =>
List_filter_inst1 Prosa_Behavior_Time_duration
  (fun A : Prosa_Behavior_Time_duration =>
   Prosa_Results_Rta_Ideal_Edf_BoundedNps_is_in_search_space_inst1
     Prosa_Implementation_Refinements_EDF_FastSearchSpace_Task
     Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_task
     Prosa_Implementation_Definitions_Task_TaskCost Prosa_Implementation_Definitions_Task_TaskDeadline ts
     Prosa_Implementation_Definitions_Task_ConcreteMaxArrivals tsk L A)
  (List_range' (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0)) L (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1)))
     : List_inst1 Prosa_Implementation_Refinements_EDF_FastSearchSpace_Task ->
       Prosa_Implementation_Refinements_EDF_FastSearchSpace_Task ->
       Prosa_Behavior_Time_duration -> List_inst1 Prosa_Behavior_Time_duration

Arguments Prosa_Implementation_Refinements_EDF_FastSearchSpace_correct_search_space ts tsk L
```
