# `task_arrivals_bound_eqdef`

- Kind (Rocq): Definition
- Rocq: `prosa.implementation.definitions.arrival_bound.task_arrivals_bound_eqdef`
- Lean: `Prosa.Implementation.Definitions.ArrivalBound.task_arrivals_bound_eqdef`
- Certificate: `ab_eqdef_bool_correspondence`

## Official Rocq

```coq
task_arrivals_bound_eqdef : task_arrivals_bound -> task_arrivals_bound -> bool

task_arrivals_bound_eqdef is not universe polymorphic
Arguments task_arrivals_bound_eqdef tb1 tb2
task_arrivals_bound_eqdef is transparent
Expands to: Constant prosa.implementation.definitions.arrival_bound.task_arrivals_bound_eqdef
Declared in library prosa.implementation.definitions.arrival_bound, line 24, characters 11-36
task_arrivals_bound_eqdef
     : task_arrivals_bound -> task_arrivals_bound -> bool
```

Body:

```coq
task_arrivals_bound_eqdef =
fun tb1 tb2 : task_arrivals_bound =>
match tb1 with
| @Periodic p1 => match tb2 with
                  | @Periodic p2 => p1 == p2
                  | _ => false
                  end
| @Sporadic s1 => match tb2 with
                  | @Sporadic s2 => s1 == s2
                  | _ => false
                  end
| @ArrivalPrefix s1 => match tb2 with
                       | @ArrivalPrefix s2 => s1 == s2
                       | _ => false
                       end
end
     : task_arrivals_bound -> task_arrivals_bound -> bool

Arguments task_arrivals_bound_eqdef tb1 tb2
```

## Lean

```lean
Prosa.Implementation.Definitions.ArrivalBound.task_arrivals_bound_eqdef : Prosa.Implementation.Definitions.ArrivalBound.task_arrivals_bound →
  Prosa.Implementation.Definitions.ArrivalBound.task_arrivals_bound → Bool
```

Body:

```lean
def Prosa.Implementation.Definitions.ArrivalBound.task_arrivals_bound_eqdef : Prosa.Implementation.Definitions.ArrivalBound.task_arrivals_bound →
  Prosa.Implementation.Definitions.ArrivalBound.task_arrivals_bound → Bool :=
fun tb1 tb2 =>
  match tb1, tb2 with
  | Prosa.Implementation.Definitions.ArrivalBound.task_arrivals_bound.Periodic p1,
    Prosa.Implementation.Definitions.ArrivalBound.task_arrivals_bound.Periodic p2 => decide (p1 = p2)
  | Prosa.Implementation.Definitions.ArrivalBound.task_arrivals_bound.Sporadic s1,
    Prosa.Implementation.Definitions.ArrivalBound.task_arrivals_bound.Sporadic s2 => decide (s1 = s2)
  | Prosa.Implementation.Definitions.ArrivalBound.task_arrivals_bound.ArrivalPrefix a1,
    Prosa.Implementation.Definitions.ArrivalBound.task_arrivals_bound.ArrivalPrefix a2 => decide (a1 = a2)
  | x, x_1 => false
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Definitions_ArrivalBound_task_arrivals_bound_eqdef
     : Prosa_Implementation_Definitions_ArrivalBound_task_arrivals_bound ->
       Prosa_Implementation_Definitions_ArrivalBound_task_arrivals_bound -> Bool
```

Body:

```coq
Prosa_Implementation_Definitions_ArrivalBound_task_arrivals_bound_eqdef@{} =
fun tb1 tb2 : Prosa_Implementation_Definitions_ArrivalBound_task_arrivals_bound =>
Prosa_Implementation_Definitions_ArrivalBound_task_arrivals_bound_eqdef_match_1
  (fun _ _ : Prosa_Implementation_Definitions_ArrivalBound_task_arrivals_bound => Bool) tb1 tb2
  (fun p1 p2 : Nat => Decidable_decide (@eq Nat p1 p2) (instDecidableEqNat p1 p2))
  (fun p1 p2 : Nat => Decidable_decide (@eq Nat p1 p2) (instDecidableEqNat p1 p2))
  (fun a1 a2 : Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_ArrivalCurvePrefix =>
   Decidable_decide (@eq Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_ArrivalCurvePrefix a1 a2)
     (instDecidableEqProd_inst3 Prosa_Behavior_Time_duration
        (List_inst1 (Prod_inst3 Prosa_Behavior_Time_duration Nat)) instDecidableEqNat
        (fun a b : List_inst1 (Prod_inst3 Prosa_Behavior_Time_duration Nat) =>
         instDecidableEqList_inst1 (Prod_inst3 Prosa_Behavior_Time_duration Nat)
           (fun a0 b0 : Prod_inst3 Prosa_Behavior_Time_duration Nat =>
            instDecidableEqProd_inst3 Prosa_Behavior_Time_duration Nat instDecidableEqNat instDecidableEqNat
              a0 b0)
           a b)
        a1 a2))
  (fun _ _ : Prosa_Implementation_Definitions_ArrivalBound_task_arrivals_bound => Bool_false)
     : Prosa_Implementation_Definitions_ArrivalBound_task_arrivals_bound ->
       Prosa_Implementation_Definitions_ArrivalBound_task_arrivals_bound -> Bool

Arguments Prosa_Implementation_Definitions_ArrivalBound_task_arrivals_bound_eqdef tb1 tb2
```
