# `task_abT_to_task_ab`

- Kind (Rocq): Definition
- Rocq: `prosa.implementation.refinements.arrival_bound.task_abT_to_task_ab`
- Lean: `Prosa.Implementation.Refinements.ArrivalBound.task_abT_to_task_ab`
- Certificate: `task_abT_to_task_ab_correspondence`

## Official Rocq

```coq
task_abT_to_task_ab : @task_arrivals_bound_T N -> task_arrivals_bound

task_abT_to_task_ab is not universe polymorphic
Arguments task_abT_to_task_ab ab
task_abT_to_task_ab is transparent
Expands to: Constant prosa.implementation.refinements.arrival_bound.task_abT_to_task_ab
Declared in library prosa.implementation.refinements.arrival_bound, line 121, characters 11-30
task_abT_to_task_ab
     : @task_arrivals_bound_T N -> task_arrivals_bound
```

Body:

```coq
task_abT_to_task_ab =
fun ab : @task_arrivals_bound_T N =>
match ab with
| @Periodic_T _ p => Periodic (nat_of_bin p)
| @Sporadic_T _ m => Sporadic (nat_of_bin m)
| @ArrivalPrefix_T _ ac_prefix_vec => ArrivalPrefix (ACPrefixT_to_ACPrefix ac_prefix_vec)
end
     : @task_arrivals_bound_T N -> task_arrivals_bound

Arguments task_abT_to_task_ab ab
```

## Lean

```lean
Prosa.Implementation.Refinements.ArrivalBound.task_abT_to_task_ab : Prosa.Implementation.Refinements.ArrivalBound.task_arrivals_bound_T
    Prosa.Implementation.Refinements.Refinements.N →
  Prosa.Implementation.Definitions.ArrivalBound.task_arrivals_bound
```

Body:

```lean
def Prosa.Implementation.Refinements.ArrivalBound.task_abT_to_task_ab : Prosa.Implementation.Refinements.ArrivalBound.task_arrivals_bound_T
    Prosa.Implementation.Refinements.Refinements.N →
  Prosa.Implementation.Definitions.ArrivalBound.task_arrivals_bound :=
fun ab =>
  match ab with
  | Prosa.Implementation.Refinements.ArrivalBound.task_arrivals_bound_T.Periodic_T p =>
    Prosa.Implementation.Definitions.ArrivalBound.task_arrivals_bound.Periodic
      (Prosa.Implementation.Refinements.Refinements.nat_of_bin p)
  | Prosa.Implementation.Refinements.ArrivalBound.task_arrivals_bound_T.Sporadic_T m =>
    Prosa.Implementation.Definitions.ArrivalBound.task_arrivals_bound.Sporadic
      (Prosa.Implementation.Refinements.Refinements.nat_of_bin m)
  | Prosa.Implementation.Refinements.ArrivalBound.task_arrivals_bound_T.ArrivalPrefix_T ac_prefix_vec =>
    Prosa.Implementation.Definitions.ArrivalBound.task_arrivals_bound.ArrivalPrefix
      (Prosa.Implementation.Refinements.ArrivalBound.ACPrefixT_to_ACPrefix ac_prefix_vec)
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_ArrivalBound_task_abT_to_task_ab
     : Prosa_Implementation_Refinements_ArrivalBound_task_arrivals_bound_T
         Prosa_Implementation_Refinements_Refinements_N ->
       Prosa_Implementation_Definitions_ArrivalBound_task_arrivals_bound
```

Body:

```coq
Prosa_Implementation_Refinements_ArrivalBound_task_abT_to_task_ab@{} =
fun
  ab : Prosa_Implementation_Refinements_ArrivalBound_task_arrivals_bound_T
         Prosa_Implementation_Refinements_Refinements_N =>
Prosa_Implementation_Refinements_ArrivalBound_task_abT_to_task_ab_match_1
  (fun
     _ : Prosa_Implementation_Refinements_ArrivalBound_task_arrivals_bound_T
           Prosa_Implementation_Refinements_Refinements_N =>
   Prosa_Implementation_Definitions_ArrivalBound_task_arrivals_bound)
  ab
  (fun p : Prosa_Implementation_Refinements_Refinements_N =>
   Prosa_Implementation_Definitions_ArrivalBound_task_arrivals_bound_Periodic
     (Prosa_Implementation_Refinements_Refinements_nat_of_bin p))
  (fun m : Prosa_Implementation_Refinements_Refinements_N =>
   Prosa_Implementation_Definitions_ArrivalBound_task_arrivals_bound_Sporadic
     (Prosa_Implementation_Refinements_Refinements_nat_of_bin m))
  (fun
     ac_prefix_vec : Prod_inst3 Prosa_Implementation_Refinements_Refinements_N
                       (List_inst1
                          (Prod_inst3 Prosa_Implementation_Refinements_Refinements_N
                             Prosa_Implementation_Refinements_Refinements_N)) =>
   Prosa_Implementation_Definitions_ArrivalBound_task_arrivals_bound_ArrivalPrefix
     (Prosa_Implementation_Refinements_ArrivalBound_ACPrefixT_to_ACPrefix ac_prefix_vec))
     : Prosa_Implementation_Refinements_ArrivalBound_task_arrivals_bound_T
         Prosa_Implementation_Refinements_Refinements_N ->
       Prosa_Implementation_Definitions_ArrivalBound_task_arrivals_bound

Arguments Prosa_Implementation_Refinements_ArrivalBound_task_abT_to_task_ab ab
```
