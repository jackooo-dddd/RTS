# `task_ab_to_task_abT`

- Kind (Rocq): Definition
- Rocq: `prosa.implementation.refinements.arrival_bound.task_ab_to_task_abT`
- Lean: `Prosa.Implementation.Refinements.ArrivalBound.task_ab_to_task_abT`
- Certificate: `task_ab_to_task_abT_correspondence`

## Official Rocq

```coq
task_ab_to_task_abT : task_arrivals_bound -> @task_arrivals_bound_T N

task_ab_to_task_abT is not universe polymorphic
Arguments task_ab_to_task_abT ab
task_ab_to_task_abT is transparent
Expands to: Constant prosa.implementation.refinements.arrival_bound.task_ab_to_task_abT
Declared in library prosa.implementation.refinements.arrival_bound, line 133, characters 11-30
task_ab_to_task_abT
     : task_arrivals_bound -> @task_arrivals_bound_T N
```

Body:

```coq
task_ab_to_task_abT =
fun ab : task_arrivals_bound =>
match ab with
| @Periodic p => @Periodic_T N (bin_of_nat p)
| @Sporadic m => @Sporadic_T N (bin_of_nat m)
| @ArrivalPrefix ac_prefix_vec => @ArrivalPrefix_T N (ACPrefix_to_ACPrefixT ac_prefix_vec)
end
     : task_arrivals_bound -> @task_arrivals_bound_T N

Arguments task_ab_to_task_abT ab
```

## Lean

```lean
Prosa.Implementation.Refinements.ArrivalBound.task_ab_to_task_abT : Prosa.Implementation.Definitions.ArrivalBound.task_arrivals_bound →
  Prosa.Implementation.Refinements.ArrivalBound.task_arrivals_bound_T Prosa.Implementation.Refinements.Refinements.N
```

Body:

```lean
def Prosa.Implementation.Refinements.ArrivalBound.task_ab_to_task_abT : Prosa.Implementation.Definitions.ArrivalBound.task_arrivals_bound →
  Prosa.Implementation.Refinements.ArrivalBound.task_arrivals_bound_T Prosa.Implementation.Refinements.Refinements.N :=
fun ab =>
  match ab with
  | Prosa.Implementation.Definitions.ArrivalBound.task_arrivals_bound.Periodic p =>
    Prosa.Implementation.Refinements.ArrivalBound.task_arrivals_bound_T.Periodic_T
      (Prosa.Implementation.Refinements.Refinements.bin_of_nat p)
  | Prosa.Implementation.Definitions.ArrivalBound.task_arrivals_bound.Sporadic m =>
    Prosa.Implementation.Refinements.ArrivalBound.task_arrivals_bound_T.Sporadic_T
      (Prosa.Implementation.Refinements.Refinements.bin_of_nat m)
  | Prosa.Implementation.Definitions.ArrivalBound.task_arrivals_bound.ArrivalPrefix ac_prefix_vec =>
    Prosa.Implementation.Refinements.ArrivalBound.task_arrivals_bound_T.ArrivalPrefix_T
      (Prosa.Implementation.Refinements.ArrivalBound.ACPrefix_to_ACPrefixT ac_prefix_vec)
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_ArrivalBound_task_ab_to_task_abT
     : Prosa_Implementation_Definitions_ArrivalBound_task_arrivals_bound ->
       Prosa_Implementation_Refinements_ArrivalBound_task_arrivals_bound_T
         Prosa_Implementation_Refinements_Refinements_N
```

Body:

```coq
Prosa_Implementation_Refinements_ArrivalBound_task_ab_to_task_abT@{} =
fun ab : Prosa_Implementation_Definitions_ArrivalBound_task_arrivals_bound =>
Prosa_Implementation_Refinements_ArrivalBound_task_ab_to_task_abT_match_1
  (fun _ : Prosa_Implementation_Definitions_ArrivalBound_task_arrivals_bound =>
   Prosa_Implementation_Refinements_ArrivalBound_task_arrivals_bound_T
     Prosa_Implementation_Refinements_Refinements_N)
  ab
  (fun p : Nat =>
   Prosa_Implementation_Refinements_ArrivalBound_task_arrivals_bound_T_Periodic_T
     Prosa_Implementation_Refinements_Refinements_N
     (Prosa_Implementation_Refinements_Refinements_bin_of_nat p))
  (fun m : Nat =>
   Prosa_Implementation_Refinements_ArrivalBound_task_arrivals_bound_T_Sporadic_T
     Prosa_Implementation_Refinements_Refinements_N
     (Prosa_Implementation_Refinements_Refinements_bin_of_nat m))
  (fun ac_prefix_vec : Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_ArrivalCurvePrefix =>
   Prosa_Implementation_Refinements_ArrivalBound_task_arrivals_bound_T_ArrivalPrefix_T
     Prosa_Implementation_Refinements_Refinements_N
     (Prosa_Implementation_Refinements_ArrivalBound_ACPrefix_to_ACPrefixT ac_prefix_vec))
     : Prosa_Implementation_Definitions_ArrivalBound_task_arrivals_bound ->
       Prosa_Implementation_Refinements_ArrivalBound_task_arrivals_bound_T
         Prosa_Implementation_Refinements_Refinements_N

Arguments Prosa_Implementation_Refinements_ArrivalBound_task_ab_to_task_abT ab
```
