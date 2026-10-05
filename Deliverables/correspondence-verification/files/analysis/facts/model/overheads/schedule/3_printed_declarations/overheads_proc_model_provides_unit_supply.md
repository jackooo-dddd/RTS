# `overheads_proc_model_provides_unit_supply`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.model.overheads.schedule.overheads_proc_model_provides_unit_supply`
- Lean: `Prosa.Analysis.Facts.Model.Overheads.Schedule.overheads_proc_model_provides_unit_supply`
- Certificate: `overheads_proc_model_provides_unit_supply_correspondence`

## Official Rocq

```coq
overheads_proc_model_provides_unit_supply :
forall {Job : JobType}, @unit_supply_proc_model Job (overheads.processor_state Job)

overheads_proc_model_provides_unit_supply is not universe polymorphic
Arguments overheads_proc_model_provides_unit_supply {Job} s
overheads_proc_model_provides_unit_supply is opaque
Expands to: Constant prosa.analysis.facts.model.overheads.schedule.overheads_proc_model_provides_unit_supply
Declared in library prosa.analysis.facts.model.overheads.schedule, line 30, characters 8-49
@overheads_proc_model_provides_unit_supply
     : forall Job : JobType, @unit_supply_proc_model Job (overheads.processor_state Job)
```

## Lean

```lean
@Prosa.Analysis.Facts.Model.Overheads.Schedule.overheads_proc_model_provides_unit_supply : ∀
  {Job : Prosa.Behavior.Job.JobType} [inst : DecidableEq Job],
  Prosa.Model.Processor.PlatformProperties.unit_supply_proc_model (Prosa.Model.Processor.Overheads.processor_state Job)
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_Overheads_Schedule_overheads_proc_model_provides_unit_supply
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : 
          DecidableEq Job),
       Prosa_Model_Processor_PlatformProperties_unit_supply_proc_model_inst4 Job
         inst_3
         (Prosa_Model_Processor_Overheads_processor_state Job
            inst_3)
```
