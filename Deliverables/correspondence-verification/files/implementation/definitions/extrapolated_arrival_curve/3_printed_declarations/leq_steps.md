# `leq_steps`

- Kind (Rocq): Definition
- Rocq: `prosa.implementation.definitions.extrapolated_arrival_curve.leq_steps`
- Lean: `Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.leq_steps`
- Certificate: `eac_leq_steps_correspondence`

## Official Rocq

```coq
leq_steps : nat * nat -> nat * nat -> bool

leq_steps is not universe polymorphic
Arguments leq_steps a b
leq_steps is transparent
Expands to: Constant prosa.implementation.definitions.extrapolated_arrival_curve.leq_steps
Declared in library prosa.implementation.definitions.extrapolated_arrival_curve, line 143, characters 11-20
leq_steps
     : nat * nat -> nat * nat -> bool
```

Body:

```coq
leq_steps = fun a b : nat * nat => (a.1 <= b.1) && (a.2 <= b.2)
     : nat * nat -> nat * nat -> bool

Arguments leq_steps a b
```

## Lean

```lean
Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.leq_steps : Prosa.Behavior.Time.duration × ℕ →
  Prosa.Behavior.Time.duration × ℕ → Bool
```

Body:

```lean
def Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.leq_steps : Prosa.Behavior.Time.duration × ℕ →
  Prosa.Behavior.Time.duration × ℕ → Bool :=
fun a b => decide (a.1 ≤ b.1) && decide (a.2 ≤ b.2)
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_leq_steps
     : Prod_inst3 Prosa_Behavior_Time_duration Nat -> Prod_inst3 Prosa_Behavior_Time_duration Nat -> Bool
```

Body:

```coq
Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_leq_steps@{} =
fun a b : Prod_inst3 Prosa_Behavior_Time_duration Nat =>
Bool_and
  (Decidable_decide
     (LE_le_inst1 Prosa_Behavior_Time_duration instLENat (Prod_fst_inst3 Prosa_Behavior_Time_duration Nat a)
        (Prod_fst_inst3 Prosa_Behavior_Time_duration Nat b))
     (Nat_decLe (Prod_fst_inst3 Prosa_Behavior_Time_duration Nat a)
        (Prod_fst_inst3 Prosa_Behavior_Time_duration Nat b)))
  (Decidable_decide
     (LE_le_inst1 Nat instLENat (Prod_snd_inst3 Prosa_Behavior_Time_duration Nat a)
        (Prod_snd_inst3 Prosa_Behavior_Time_duration Nat b))
     (Nat_decLe (Prod_snd_inst3 Prosa_Behavior_Time_duration Nat a)
        (Prod_snd_inst3 Prosa_Behavior_Time_duration Nat b)))
     : Prod_inst3 Prosa_Behavior_Time_duration Nat -> Prod_inst3 Prosa_Behavior_Time_duration Nat -> Bool

Arguments Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_leq_steps a b
```
