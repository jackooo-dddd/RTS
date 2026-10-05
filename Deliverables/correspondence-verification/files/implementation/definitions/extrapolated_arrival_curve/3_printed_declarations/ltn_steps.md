# `ltn_steps`

- Kind (Rocq): Definition
- Rocq: `prosa.implementation.definitions.extrapolated_arrival_curve.ltn_steps`
- Lean: `Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.ltn_steps`
- Certificate: `eac_ltn_steps_correspondence`

## Official Rocq

```coq
ltn_steps : nat * nat -> nat * nat -> bool

ltn_steps is not universe polymorphic
Arguments ltn_steps a b
ltn_steps is transparent
Expands to: Constant prosa.implementation.definitions.extrapolated_arrival_curve.ltn_steps
Declared in library prosa.implementation.definitions.extrapolated_arrival_curve, line 107, characters 11-20
ltn_steps
     : nat * nat -> nat * nat -> bool
```

Body:

```coq
ltn_steps = fun a b : nat * nat => (a.1 < b.1) && (a.2 < b.2)
     : nat * nat -> nat * nat -> bool

Arguments ltn_steps a b
```

## Lean

```lean
Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.ltn_steps : Prosa.Behavior.Time.duration × ℕ →
  Prosa.Behavior.Time.duration × ℕ → Bool
```

Body:

```lean
def Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.ltn_steps : Prosa.Behavior.Time.duration × ℕ →
  Prosa.Behavior.Time.duration × ℕ → Bool :=
fun a b => decide (a.1 < b.1) && decide (a.2 < b.2)
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_ltn_steps
     : Prod_inst3 Prosa_Behavior_Time_duration Nat -> Prod_inst3 Prosa_Behavior_Time_duration Nat -> Bool
```

Body:

```coq
Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_ltn_steps@{} =
fun a b : Prod_inst3 Prosa_Behavior_Time_duration Nat =>
Bool_and
  (Decidable_decide
     (LT_lt_inst1 Prosa_Behavior_Time_duration instLTNat (Prod_fst_inst3 Prosa_Behavior_Time_duration Nat a)
        (Prod_fst_inst3 Prosa_Behavior_Time_duration Nat b))
     (Nat_decLt (Prod_fst_inst3 Prosa_Behavior_Time_duration Nat a)
        (Prod_fst_inst3 Prosa_Behavior_Time_duration Nat b)))
  (Decidable_decide
     (LT_lt_inst1 Nat instLTNat (Prod_snd_inst3 Prosa_Behavior_Time_duration Nat a)
        (Prod_snd_inst3 Prosa_Behavior_Time_duration Nat b))
     (Nat_decLt (Prod_snd_inst3 Prosa_Behavior_Time_duration Nat a)
        (Prod_snd_inst3 Prosa_Behavior_Time_duration Nat b)))
     : Prod_inst3 Prosa_Behavior_Time_duration Nat -> Prod_inst3 Prosa_Behavior_Time_duration Nat -> Bool

Arguments Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_ltn_steps a b
```
