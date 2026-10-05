# `ideal_proc_model_fully_consuming`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.model.ideal.schedule.ideal_proc_model_fully_consuming`
- Lean: `Prosa.Analysis.Facts.Model.Ideal.Schedule.ideal_proc_model_fully_consuming`
- Certificate: `ideal_proc_model_fully_consuming_correspondence`

## Official Rocq

```coq
ideal_proc_model_fully_consuming :
forall {Job : JobType}, @fully_consuming_proc_model Job (ideal.processor_state Job)

ideal_proc_model_fully_consuming is not universe polymorphic
Arguments ideal_proc_model_fully_consuming {Job} j s t _
ideal_proc_model_fully_consuming is opaque
Expands to: Constant prosa.analysis.facts.model.ideal.schedule.ideal_proc_model_fully_consuming
Declared in library prosa.analysis.facts.model.ideal.schedule, line 126, characters 8-40
@ideal_proc_model_fully_consuming
     : forall Job : JobType, @fully_consuming_proc_model Job (ideal.processor_state Job)
```

## Lean

```lean
Prosa.Analysis.Facts.Model.Ideal.Schedule.ideal_proc_model_fully_consuming : ∀ (Job : Prosa.Behavior.Job.JobType)
  [inst : DecidableEq Job],
  Prosa.Model.Processor.PlatformProperties.fully_consuming_proc_model (Prosa.Model.Processor.Ideal.processor_state Job)
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_Ideal_Schedule_ideal_proc_model_fully_consuming
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Model_Processor_PlatformProperties_fully_consuming_proc_model_inst4 Job
         inst_3
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_3)
```
