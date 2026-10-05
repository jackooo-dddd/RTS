# `unit_supply_bound_function`

- Kind (Rocq): Definition
- Rocq: `prosa.analysis.definitions.sbf.pred.unit_supply_bound_function`
- Lean: `Prosa.Analysis.Definitions.Sbf.Pred.unit_supply_bound_function`
- Certificate: `pred_unit_supply_bound_function_correspondence`

## Official Rocq

```coq
unit_supply_bound_function : (duration -> work) -> Prop

unit_supply_bound_function is not universe polymorphic
Arguments unit_supply_bound_function SBF%function_scope
unit_supply_bound_function is transparent
Expands to: Constant prosa.analysis.definitions.sbf.pred.unit_supply_bound_function
Declared in library prosa.analysis.definitions.sbf.pred, line 61, characters 13-39
unit_supply_bound_function
     : (duration -> work) -> Prop
```

Body:

```coq
unit_supply_bound_function =
fun SBF : duration -> work => forall δ : duration, is_true (SBF δ.+1 <= (SBF δ).+1)
     : (duration -> work) -> Prop

Arguments unit_supply_bound_function SBF%function_scope
```

## Lean

```lean
Prosa.Analysis.Definitions.Sbf.Pred.unit_supply_bound_function : (Prosa.Behavior.Time.duration →
    Prosa.Behavior.Job.work) →
  Prop
```

Body:

```lean
def Prosa.Analysis.Definitions.Sbf.Pred.unit_supply_bound_function : (Prosa.Behavior.Time.duration →
    Prosa.Behavior.Job.work) →
  Prop :=
fun SBF => ∀ (δ : Prosa.Behavior.Time.duration), SBF (δ + 1) ≤ SBF δ + 1
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Definitions_Sbf_Pred_unit_supply_bound_function
     : (Prosa_Behavior_Time_duration -> Prosa_Behavior_Job_work) -> SProp
```

Body:

```coq
Prosa_Analysis_Definitions_Sbf_Pred_unit_supply_bound_function@{} =
fun SBF : Prosa_Behavior_Time_duration -> Prosa_Behavior_Job_work =>
forall _UU03b4_ : Prosa_Behavior_Time_duration,
LE_le_inst1 Prosa_Behavior_Job_work instLENat
  (SBF
     (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
        (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) _UU03b4_
        (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 1 (instOfNatNat 1))))
  (HAdd_hAdd_inst7 Prosa_Behavior_Job_work Prosa_Behavior_Job_work Prosa_Behavior_Job_work
     (instHAdd_inst1 Prosa_Behavior_Job_work instAddNat) (SBF _UU03b4_)
     (OfNat_ofNat_inst1 Prosa_Behavior_Job_work 1 (instOfNatNat 1)))
     : (Prosa_Behavior_Time_duration -> Prosa_Behavior_Job_work) -> SProp

Arguments Prosa_Analysis_Definitions_Sbf_Pred_unit_supply_bound_function SBF%_function_scope
```
