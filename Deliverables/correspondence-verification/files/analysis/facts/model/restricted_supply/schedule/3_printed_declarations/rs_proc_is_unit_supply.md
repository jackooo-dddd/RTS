# `rs_proc_is_unit_supply`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.model.restricted_supply.schedule.rs_proc_is_unit_supply`
- Lean: `Prosa.Analysis.Facts.Model.RestrictedSupply.Schedule.rs_proc_is_unit_supply`
- Certificate: `facts_unit_supply_model_correspondence`

## Official Rocq

```coq
rs_proc_is_unit_supply : forall {Job : JobType}, @unit_supply_proc_model Job (rs_processor_state Job)

rs_proc_is_unit_supply is not universe polymorphic
Arguments rs_proc_is_unit_supply {Job} s
rs_proc_is_unit_supply is opaque
Expands to: Constant prosa.analysis.facts.model.restricted_supply.schedule.rs_proc_is_unit_supply
Declared in library prosa.analysis.facts.model.restricted_supply.schedule, line 28, characters 8-30
@rs_proc_is_unit_supply
     : forall Job : JobType, @unit_supply_proc_model Job (rs_processor_state Job)
```

## Lean

```lean
@Prosa.Analysis.Facts.Model.RestrictedSupply.Schedule.rs_proc_is_unit_supply : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job],
  Prosa.Model.Processor.PlatformProperties.unit_supply_proc_model
    (Prosa.Model.Processor.RestrictedSupply.rs_processor_state Job)
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_RestrictedSupply_Schedule_rs_proc_is_unit_supply
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : 
          DecidableEq Job),
       Prosa_Model_Processor_PlatformProperties_unit_supply_proc_model_inst4 Job
         inst_3
         (Prosa_Model_Processor_RestrictedSupply_rs_processor_state Job
            inst_3)
```
