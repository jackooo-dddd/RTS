# `arm_sbf`

- Kind (Rocq): Definition
- Rocq: `prosa.analysis.definitions.sbf.average.arm_sbf`
- Lean: `Prosa.Analysis.Definitions.Sbf.Average.arm_sbf`
- Certificate: `arm_sbf_correspondence`

## Official Rocq

```coq
arm_sbf : duration -> duration -> duration -> nat -> nat

arm_sbf is not universe polymorphic
Arguments arm_sbf Π Θ ν Δ%nat_scope
arm_sbf is transparent
Expands to: Constant prosa.analysis.definitions.sbf.average.arm_sbf
Declared in library prosa.analysis.definitions.sbf.average, line 50, characters 13-20
arm_sbf
     : duration -> duration -> duration -> nat -> nat
```

Body:

```coq
arm_sbf =
fun (Π Θ ν : duration) (Δ : nat) => ((Δ - ν) * Θ) %/ Π
     : duration -> duration -> duration -> nat -> nat

Arguments arm_sbf Π Θ ν Δ%nat_scope
```

## Lean

```lean
Prosa.Analysis.Definitions.Sbf.Average.arm_sbf : Prosa.Behavior.Time.duration →
  Prosa.Behavior.Time.duration →
    Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration
```

Body:

```lean
def Prosa.Analysis.Definitions.Sbf.Average.arm_sbf : Prosa.Behavior.Time.duration →
  Prosa.Behavior.Time.duration →
    Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration :=
fun period allocation delay delta => (delta - delay) * allocation / period
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Definitions_Sbf_Average_arm_sbf
     : Prosa_Behavior_Time_duration ->
       Prosa_Behavior_Time_duration ->
       Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration
```

Body:

```coq
Prosa_Analysis_Definitions_Sbf_Average_arm_sbf@{} =
fun period allocation delay delta : Prosa_Behavior_Time_duration =>
HDiv_hDiv_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
  (instHDiv_inst1 Prosa_Behavior_Time_duration Nat_instDiv)
  (HMul_hMul_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
     (instHMul_inst1 Prosa_Behavior_Time_duration instMulNat)
     (HSub_hSub_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
        (instHSub_inst1 Prosa_Behavior_Time_duration instSubNat) delta delay)
     allocation)
  period
     : Prosa_Behavior_Time_duration ->
       Prosa_Behavior_Time_duration ->
       Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration

Arguments Prosa_Analysis_Definitions_Sbf_Average_arm_sbf period allocation delay delta
```
