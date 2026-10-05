# `overheads_proc_model_is_a_uniprocessor_model`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.model.overheads.schedule.overheads_proc_model_is_a_uniprocessor_model`
- Lean: `Prosa.Analysis.Facts.Model.Overheads.Schedule.overheads_proc_model_is_a_uniprocessor_model`
- Certificate: `overheads_proc_model_is_a_uniprocessor_model_correspondence`

## Official Rocq

```coq
overheads_proc_model_is_a_uniprocessor_model :
forall {Job : JobType}, @uniprocessor_model Job (overheads.processor_state Job)

overheads_proc_model_is_a_uniprocessor_model is not universe polymorphic
Arguments overheads_proc_model_is_a_uniprocessor_model {Job} j1 j2 s t _ _
overheads_proc_model_is_a_uniprocessor_model is opaque
Expands to: Constant
            prosa.analysis.facts.model.overheads.schedule.overheads_proc_model_is_a_uniprocessor_model
Declared in library prosa.analysis.facts.model.overheads.schedule, line 17, characters 8-52
@overheads_proc_model_is_a_uniprocessor_model
     : forall Job : JobType, @uniprocessor_model Job (overheads.processor_state Job)
```

## Lean

```lean
@Prosa.Analysis.Facts.Model.Overheads.Schedule.overheads_proc_model_is_a_uniprocessor_model : ∀
  {Job : Prosa.Behavior.Job.JobType} [inst : DecidableEq Job],
  Prosa.Model.Processor.PlatformProperties.uniprocessor_model (Prosa.Model.Processor.Overheads.processor_state Job)
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_Overheads_Schedule_overheads_proc_model_is_a_uniprocessor_model
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : 
          DecidableEq Job),
       Prosa_Model_Processor_PlatformProperties_uniprocessor_model_inst4 Job
         inst_3
         (Prosa_Model_Processor_Overheads_processor_state Job
            inst_3)
```
