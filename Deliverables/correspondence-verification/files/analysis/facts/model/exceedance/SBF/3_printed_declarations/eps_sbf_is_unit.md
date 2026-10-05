# `eps_sbf_is_unit`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.model.exceedance.SBF.eps_sbf_is_unit`
- Lean: `Prosa.Analysis.Facts.Model.Exceedance.SBF.eps_sbf_is_unit`
- Certificate: `eps_sbf_is_unit_correspondence`

## Official Rocq

```coq
eps_sbf_is_unit : forall e : work, unit_supply_bound_function (EPS_SBF_inst e)

eps_sbf_is_unit is not universe polymorphic
Arguments eps_sbf_is_unit e δ
eps_sbf_is_unit is opaque
Expands to: Constant prosa.analysis.facts.model.exceedance.SBF.eps_sbf_is_unit
Declared in library prosa.analysis.facts.model.exceedance.SBF, line 96, characters 8-23
eps_sbf_is_unit
     : forall e : work, unit_supply_bound_function (EPS_SBF_inst e)
```

## Lean

```lean
Prosa.Analysis.Facts.Model.Exceedance.SBF.eps_sbf_is_unit : ∀ (e : Prosa.Behavior.Job.work),
  Prosa.Analysis.Definitions.Sbf.Pred.unit_supply_bound_function
    Prosa.Analysis.Definitions.Sbf.SupplyBoundFunction.supply_bound_function
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_Exceedance_SBF_eps_sbf_is_unit
     : forall e : Prosa_Behavior_Job_work,
       Prosa_Analysis_Definitions_Sbf_Pred_unit_supply_bound_function
         (Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction_supply_bound_function
            (Prosa_Analysis_Facts_Model_Exceedance_SBF_EPS_SBF_inst e))
```
