# `overheads_proc_model_fully_consuming`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.model.overheads.schedule.overheads_proc_model_fully_consuming`
- Lean: `Prosa.Analysis.Facts.Model.Overheads.Schedule.overheads_proc_model_fully_consuming`
- Certificate: `overheads_proc_model_fully_consuming_correspondence`

## Official Rocq

```coq
overheads_proc_model_fully_consuming :
forall {Job : JobType}, @fully_consuming_proc_model Job (overheads.processor_state Job)

overheads_proc_model_fully_consuming is not universe polymorphic
Arguments overheads_proc_model_fully_consuming {Job} j s t _
overheads_proc_model_fully_consuming is opaque
Expands to: Constant prosa.analysis.facts.model.overheads.schedule.overheads_proc_model_fully_consuming
Declared in library prosa.analysis.facts.model.overheads.schedule, line 40, characters 8-44
@overheads_proc_model_fully_consuming
     : forall Job : JobType, @fully_consuming_proc_model Job (overheads.processor_state Job)
```

## Lean

```lean
@Prosa.Analysis.Facts.Model.Overheads.Schedule.overheads_proc_model_fully_consuming : ∀
  {Job : Prosa.Behavior.Job.JobType} [inst : DecidableEq Job],
  Prosa.Model.Processor.PlatformProperties.fully_consuming_proc_model
    (Prosa.Model.Processor.Overheads.processor_state Job)
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_Overheads_Schedule_overheads_proc_model_fully_consuming
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : 
          DecidableEq Job),
       Prosa_Model_Processor_PlatformProperties_fully_consuming_proc_model_inst4 Job
         inst_3
         (Prosa_Model_Processor_Overheads_processor_state Job
            inst_3)
```
