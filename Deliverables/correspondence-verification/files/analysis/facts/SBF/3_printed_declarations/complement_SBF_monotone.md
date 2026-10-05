# `complement_SBF_monotone`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.SBF.complement_SBF_monotone`
- Lean: `Prosa.Analysis.Facts.SBF.complement_SBF_monotone`
- Certificate: `complement_SBF_monotone_correspondence`

## Official Rocq

```coq
complement_SBF_monotone :
forall {SBF : SupplyBoundFunction},
unit_supply_bound_function SBF ->
forall Δ1 Δ2 : nat, is_true (Δ1 <= Δ2) -> is_true (Δ1 - SBF Δ1 <= Δ2 - SBF Δ2)

complement_SBF_monotone is not universe polymorphic
Arguments complement_SBF_monotone {SBF} H_unit_SBF (Δ1 Δ2)%nat_scope _
complement_SBF_monotone is opaque
Expands to: Constant prosa.analysis.facts.SBF.complement_SBF_monotone
Declared in library prosa.analysis.facts.SBF, line 106, characters 10-33
@complement_SBF_monotone
     : forall SBF : SupplyBoundFunction,
       unit_supply_bound_function SBF ->
       forall Δ1 Δ2 : nat, is_true (Δ1 <= Δ2) -> is_true (Δ1 - SBF Δ1 <= Δ2 - SBF Δ2)
```

## Lean

```lean
@Prosa.Analysis.Facts.SBF.complement_SBF_monotone : ∀ {SBF : Prosa.Analysis.Definitions.Sbf.SupplyBoundFunction},
  Prosa.Analysis.Definitions.Sbf.Pred.unit_supply_bound_function
      Prosa.Analysis.Definitions.Sbf.SupplyBoundFunction.supply_bound_function →
    ∀ {Δ1 Δ2 : Prosa.Behavior.Time.duration},
      Δ1 ≤ Δ2 →
        Δ1 - Prosa.Analysis.Definitions.Sbf.SupplyBoundFunction.supply_bound_function Δ1 ≤
          Δ2 - Prosa.Analysis.Definitions.Sbf.SupplyBoundFunction.supply_bound_function Δ2
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_SBF_complement_SBF_monotone
     : forall SBF : Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction,
       Prosa_Analysis_Definitions_Sbf_Pred_unit_supply_bound_function
         (Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction_supply_bound_function SBF) ->
       forall _UU0394_1 _UU0394_2 : Prosa_Behavior_Time_duration,
       LE_le_inst1 Prosa_Behavior_Time_duration instLENat _UU0394_1 _UU0394_2 ->
       LE_le_inst1 Prosa_Behavior_Time_duration instLENat
         (HSub_hSub_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Job_work Prosa_Behavior_Time_duration
            (instHSub_inst1 Prosa_Behavior_Time_duration instSubNat) _UU0394_1
            (Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction_supply_bound_function SBF _UU0394_1))
         (HSub_hSub_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Job_work Prosa_Behavior_Time_duration
            (instHSub_inst1 Prosa_Behavior_Time_duration instSubNat) _UU0394_2
            (Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction_supply_bound_function SBF _UU0394_2))
```
