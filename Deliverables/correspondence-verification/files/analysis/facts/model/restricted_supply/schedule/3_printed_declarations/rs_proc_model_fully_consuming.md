# `rs_proc_model_fully_consuming`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.model.restricted_supply.schedule.rs_proc_model_fully_consuming`
- Lean: `Prosa.Analysis.Facts.Model.RestrictedSupply.Schedule.rs_proc_model_fully_consuming`
- Certificate: `facts_fully_consuming_model_correspondence`

## Official Rocq

```coq
rs_proc_model_fully_consuming :
forall {Job : JobType}, @fully_consuming_proc_model Job (rs_processor_state Job)

rs_proc_model_fully_consuming is not universe polymorphic
Arguments rs_proc_model_fully_consuming {Job} j s t _
rs_proc_model_fully_consuming is opaque
Expands to: Constant prosa.analysis.facts.model.restricted_supply.schedule.rs_proc_model_fully_consuming
Declared in library prosa.analysis.facts.model.restricted_supply.schedule, line 37, characters 8-37
@rs_proc_model_fully_consuming
     : forall Job : JobType, @fully_consuming_proc_model Job (rs_processor_state Job)
```

## Lean

```lean
@Prosa.Analysis.Facts.Model.RestrictedSupply.Schedule.rs_proc_model_fully_consuming : ∀
  {Job : Prosa.Behavior.Job.JobType} [inst : DecidableEq Job],
  Prosa.Model.Processor.PlatformProperties.fully_consuming_proc_model
    (Prosa.Model.Processor.RestrictedSupply.rs_processor_state Job)
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_RestrictedSupply_Schedule_rs_proc_model_fully_consuming
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : 
          DecidableEq Job),
       Prosa_Model_Processor_PlatformProperties_fully_consuming_proc_model_inst4 Job
         inst_3
         (Prosa_Model_Processor_RestrictedSupply_rs_processor_state Job
            inst_3)
```
