# `arm_sbf_monotone`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.model.sbf.average.arm_sbf_monotone`
- Lean: `Prosa.Analysis.Facts.Model.Sbf.Average.arm_sbf_monotone`
- Certificate: `arm_sbf_monotone_correspondence`

## Official Rocq

```coq
arm_sbf_monotone : forall Π Θ ν : duration, sbf_is_monotone (arm_sbf Π Θ ν)

arm_sbf_monotone is not universe polymorphic
Arguments arm_sbf_monotone Π Θ ν x y _
arm_sbf_monotone is opaque
Expands to: Constant prosa.analysis.facts.model.sbf.average.arm_sbf_monotone
Declared in library prosa.analysis.facts.model.sbf.average, line 41, characters 8-24
arm_sbf_monotone
     : forall Π Θ ν : duration, sbf_is_monotone (arm_sbf Π Θ ν)
```

## Lean

```lean
Prosa.Analysis.Facts.Model.Sbf.Average.arm_sbf_monotone : ∀ (period alloc delay : Prosa.Behavior.Time.duration),
  Prosa.Analysis.Definitions.Sbf.Pred.sbf_is_monotone
    (Prosa.Analysis.Definitions.Sbf.Average.arm_sbf period alloc delay)
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_Sbf_Average_arm_sbf_monotone
     : forall period alloc delay : Prosa_Behavior_Time_duration,
       Prosa_Analysis_Definitions_Sbf_Pred_sbf_is_monotone
         (Prosa_Analysis_Definitions_Sbf_Average_arm_sbf period alloc delay)
```
