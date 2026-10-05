# `unit_supply_is_unit_service`

- Kind (Rocq): Remark
- Rocq: `prosa.model.processor.platform_properties.unit_supply_is_unit_service`
- Lean: `Prosa.Model.Processor.PlatformProperties.unit_supply_is_unit_service`
- Certificate: `unit_supply_is_unit_service_statement_correspondence`

## Official Rocq

```coq
unit_supply_is_unit_service :
forall {Job : JobType} (PState : ProcessorState Job),
@unit_supply_proc_model Job PState -> @unit_service_proc_model Job PState

unit_supply_is_unit_service is not universe polymorphic
Arguments unit_supply_is_unit_service {Job} PState _ j s
unit_supply_is_unit_service is opaque
Expands to: Constant prosa.model.processor.platform_properties.unit_supply_is_unit_service
Declared in library prosa.model.processor.platform_properties, line 44, characters 9-36
@unit_supply_is_unit_service
     : forall (Job : JobType) (PState : ProcessorState Job),
       @unit_supply_proc_model Job PState -> @unit_service_proc_model Job PState
```

## Lean

```lean
@Prosa.Model.Processor.PlatformProperties.unit_supply_is_unit_service : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] (PState : Prosa.Behavior.Schedule.ProcessorState Job),
  Prosa.Model.Processor.PlatformProperties.unit_supply_proc_model PState →
    Prosa.Model.Processor.PlatformProperties.unit_service_proc_model PState
```

## Lean, imported into Rocq

```coq
Prosa_Model_Processor_PlatformProperties_unit_supply_is_unit_service
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3),
       Prosa_Model_Processor_PlatformProperties_unit_supply_proc_model Job
         inst_3 PState ->
       Prosa_Model_Processor_PlatformProperties_unit_service_proc_model Job
         inst_3 PState
```
