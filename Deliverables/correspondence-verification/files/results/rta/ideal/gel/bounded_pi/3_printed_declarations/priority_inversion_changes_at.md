# `priority_inversion_changes_at`

- Kind (Rocq): Definition
- Rocq: `prosa.results.rta.ideal.gel.bounded_pi.priority_inversion_changes_at`
- Lean: `Prosa.Results.Rta.Ideal.Gel.BoundedPi.priority_inversion_changes_at`
- Certificate: `priority_inversion_changes_at_correspondence`

## Official Rocq

```coq
priority_inversion_changes_at : (duration -> duration) -> duration -> bool

priority_inversion_changes_at is not universe polymorphic
Arguments priority_inversion_changes_at priority_inversion_bound%function_scope A
priority_inversion_changes_at is transparent
Expands to: Constant prosa.results.rta.ideal.gel.bounded_pi.priority_inversion_changes_at
Declared in library prosa.results.rta.ideal.gel.bounded_pi, line 267, characters 13-42
priority_inversion_changes_at
     : (duration -> duration) -> duration -> bool
```

Body:

```coq
priority_inversion_changes_at =
fun (priority_inversion_bound : duration -> duration) (A : duration) =>
priority_inversion_bound (A - 1) != priority_inversion_bound A
     : (duration -> duration) -> duration -> bool

Arguments priority_inversion_changes_at priority_inversion_bound%function_scope A
```

## Lean

```lean
Prosa.Results.Rta.Ideal.Gel.BoundedPi.priority_inversion_changes_at : (Prosa.Behavior.Time.duration →
    Prosa.Behavior.Time.duration) →
  Prosa.Behavior.Time.duration → Bool
```

Body:

```lean
def Prosa.Results.Rta.Ideal.Gel.BoundedPi.priority_inversion_changes_at : (Prosa.Behavior.Time.duration →
    Prosa.Behavior.Time.duration) →
  Prosa.Behavior.Time.duration → Bool :=
fun priority_inversion_bound A => decide (priority_inversion_bound (A - 1) ≠ priority_inversion_bound A)
```

## Lean, imported into Rocq

```coq
Prosa_Results_Rta_Ideal_Gel_BoundedPi_priority_inversion_changes_at
     : (Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration) -> Prosa_Behavior_Time_duration -> Bool
```

Body:

```coq
Prosa_Results_Rta_Ideal_Gel_BoundedPi_priority_inversion_changes_at@{} =
fun (priority_inversion_bound : Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration)
  (A : Prosa_Behavior_Time_duration) =>
Decidable_decide
  (Ne Prosa_Behavior_Time_duration
     (priority_inversion_bound
        (HSub_hSub_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
           Prosa_Behavior_Time_duration (instHSub_inst1 Prosa_Behavior_Time_duration instSubNat) A
           (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 1 (instOfNatNat 1))))
     (priority_inversion_bound A))
  (instDecidableNot
     (@eq Prosa_Behavior_Time_duration
        (priority_inversion_bound
           (HSub_hSub_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
              Prosa_Behavior_Time_duration (instHSub_inst1 Prosa_Behavior_Time_duration instSubNat) A
              (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 1 (instOfNatNat 1))))
        (priority_inversion_bound A))
     (instDecidableEqNat
        (priority_inversion_bound
           (HSub_hSub_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
              Prosa_Behavior_Time_duration (instHSub_inst1 Prosa_Behavior_Time_duration instSubNat) A
              (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 1 (instOfNatNat 1))))
        (priority_inversion_bound A)))
     : (Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration) -> Prosa_Behavior_Time_duration -> Bool

Arguments Prosa_Results_Rta_Ideal_Gel_BoundedPi_priority_inversion_changes_at
  priority_inversion_bound%_function_scope R
```
