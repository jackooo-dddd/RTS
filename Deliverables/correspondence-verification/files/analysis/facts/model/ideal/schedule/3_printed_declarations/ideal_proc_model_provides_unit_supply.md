# `ideal_proc_model_provides_unit_supply`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.model.ideal.schedule.ideal_proc_model_provides_unit_supply`
- Lean: `Prosa.Analysis.Facts.Model.Ideal.Schedule.ideal_proc_model_provides_unit_supply`
- Certificate: `ideal_proc_model_provides_unit_supply_correspondence`

## Official Rocq

```coq
ideal_proc_model_provides_unit_supply :
forall {Job : JobType}, @unit_supply_proc_model Job (ideal.processor_state Job)

ideal_proc_model_provides_unit_supply is not universe polymorphic
Arguments ideal_proc_model_provides_unit_supply {Job} s
ideal_proc_model_provides_unit_supply is opaque
Expands to: Constant prosa.analysis.facts.model.ideal.schedule.ideal_proc_model_provides_unit_supply
Declared in library prosa.analysis.facts.model.ideal.schedule, line 74, characters 8-45
@ideal_proc_model_provides_unit_supply
     : forall Job : JobType, @unit_supply_proc_model Job (ideal.processor_state Job)
```

## Lean

```lean
Prosa.Analysis.Facts.Model.Ideal.Schedule.ideal_proc_model_provides_unit_supply : ∀ (Job : Prosa.Behavior.Job.JobType)
  [inst : DecidableEq Job],
  Prosa.Model.Processor.PlatformProperties.unit_supply_proc_model (Prosa.Model.Processor.Ideal.processor_state Job)
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_Ideal_Schedule_ideal_proc_model_provides_unit_supply
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Model_Processor_PlatformProperties_unit_supply_proc_model_inst4 Job
         inst_3
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_3)
```
