# `eps_is_unit_supply`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.model.ideal_uni_exceed.eps_is_unit_supply`
- Lean: `Prosa.Analysis.Facts.Model.IdealUniExceed.eps_is_unit_supply`
- Certificate: `facts_unit_supply_model_correspondence`

## Official Rocq

```coq
eps_is_unit_supply :
forall {Job : JobType}, @unit_supply_proc_model Job (ideal_uni_exceed.exceedance_proc_state Job)

eps_is_unit_supply is not universe polymorphic
Arguments eps_is_unit_supply {Job} s
eps_is_unit_supply is opaque
Expands to: Constant prosa.analysis.facts.model.ideal_uni_exceed.eps_is_unit_supply
Declared in library prosa.analysis.facts.model.ideal_uni_exceed, line 12, characters 8-26
@eps_is_unit_supply
     : forall Job : JobType, @unit_supply_proc_model Job (ideal_uni_exceed.exceedance_proc_state Job)
```

## Lean

```lean
@Prosa.Analysis.Facts.Model.IdealUniExceed.eps_is_unit_supply : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job],
  Prosa.Model.Processor.PlatformProperties.unit_supply_proc_model
    (Prosa.Model.Processor.IdealUniExceed.exceedance_proc_state Job)
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_IdealUniExceed_eps_is_unit_supply
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Model_Processor_PlatformProperties_unit_supply_proc_model_inst4 Job
         inst_3
         (Prosa_Model_Processor_IdealUniExceed_exceedance_proc_state Job
            inst_3)
```
