# `prm_sbf`

- Kind (Rocq): Definition
- Rocq: `prosa.analysis.definitions.sbf.periodic.prm_sbf`
- Lean: `Prosa.Analysis.Definitions.Sbf.Periodic.prm_sbf`
- Certificate: `prm_sbf_correspondence`

## Official Rocq

```coq
prm_sbf : duration -> duration -> nat -> nat

prm_sbf is not universe polymorphic
Arguments prm_sbf Π γ Δ%nat_scope
prm_sbf is transparent
Expands to: Constant prosa.analysis.definitions.sbf.periodic.prm_sbf
Declared in library prosa.analysis.definitions.sbf.periodic, line 37, characters 13-20
prm_sbf
     : duration -> duration -> nat -> nat
```

Body:

```coq
prm_sbf =
fun (Π γ : duration) (Δ : nat) =>
let blackout := Π - γ in
let n_full_periods := (Δ - blackout) %/ Π in
let supply_in_full_periods := n_full_periods * γ in
let duration_of_full_periods := n_full_periods * Π in
supply_in_full_periods + (Δ - 2 * blackout - duration_of_full_periods)
     : duration -> duration -> nat -> nat

Arguments prm_sbf Π γ Δ%nat_scope
```

## Lean

```lean
Prosa.Analysis.Definitions.Sbf.Periodic.prm_sbf : Prosa.Behavior.Time.duration →
  Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration
```

Body:

```lean
def Prosa.Analysis.Definitions.Sbf.Periodic.prm_sbf : Prosa.Behavior.Time.duration →
  Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration :=
fun period allocation delta =>
  have blackout := period - allocation;
  have n_full_periods := (delta - blackout) / period;
  have supply_in_full_periods := n_full_periods * allocation;
  have duration_of_full_periods := n_full_periods * period;
  supply_in_full_periods + (delta - 2 * blackout - duration_of_full_periods)
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Definitions_Sbf_Periodic_prm_sbf
     : Prosa_Behavior_Time_duration ->
       Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration
```

Body:

```coq
Prosa_Analysis_Definitions_Sbf_Periodic_prm_sbf@{} =
fun period allocation delta : Prosa_Behavior_Time_duration =>
let blackout :=
  HSub_hSub_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
    (instHSub_inst1 Prosa_Behavior_Time_duration instSubNat) period allocation
  in
let n_full_periods :=
  HDiv_hDiv_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
    (instHDiv_inst1 Prosa_Behavior_Time_duration Nat_instDiv)
    (HSub_hSub_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
       (instHSub_inst1 Prosa_Behavior_Time_duration instSubNat) delta blackout)
    period
  in
let supply_in_full_periods :=
  HMul_hMul_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
    (instHMul_inst1 Prosa_Behavior_Time_duration instMulNat) n_full_periods allocation
  in
let duration_of_full_periods :=
  HMul_hMul_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
    (instHMul_inst1 Prosa_Behavior_Time_duration instMulNat) n_full_periods period
  in
HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
  (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) supply_in_full_periods
  (HSub_hSub_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
     (instHSub_inst1 Prosa_Behavior_Time_duration instSubNat)
     (HSub_hSub_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
        (instHSub_inst1 Prosa_Behavior_Time_duration instSubNat) delta
        (HMul_hMul_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
           Prosa_Behavior_Time_duration (instHMul_inst1 Prosa_Behavior_Time_duration instMulNat)
           (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 2 (instOfNatNat 2)) blackout))
     duration_of_full_periods)
     : Prosa_Behavior_Time_duration ->
       Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration

Arguments Prosa_Analysis_Definitions_Sbf_Periodic_prm_sbf period allocation delta
```
