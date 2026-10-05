# `ideal_proc_model_is_a_uniprocessor_model`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.model.ideal.schedule.ideal_proc_model_is_a_uniprocessor_model`
- Lean: `Prosa.Analysis.Facts.Model.Ideal.Schedule.ideal_proc_model_is_a_uniprocessor_model`
- Certificate: `ideal_proc_model_is_a_uniprocessor_model_correspondence`

## Official Rocq

```coq
ideal_proc_model_is_a_uniprocessor_model :
forall {Job : JobType}, @uniprocessor_model Job (ideal.processor_state Job)

ideal_proc_model_is_a_uniprocessor_model is not universe polymorphic
Arguments ideal_proc_model_is_a_uniprocessor_model {Job} j1 j2 s t _ _
ideal_proc_model_is_a_uniprocessor_model is opaque
Expands to: Constant prosa.analysis.facts.model.ideal.schedule.ideal_proc_model_is_a_uniprocessor_model
Declared in library prosa.analysis.facts.model.ideal.schedule, line 24, characters 8-48
@ideal_proc_model_is_a_uniprocessor_model
     : forall Job : JobType, @uniprocessor_model Job (ideal.processor_state Job)
```

## Lean

```lean
Prosa.Analysis.Facts.Model.Ideal.Schedule.ideal_proc_model_is_a_uniprocessor_model : ∀
  (Job : Prosa.Behavior.Job.JobType) [inst : DecidableEq Job],
  Prosa.Model.Processor.PlatformProperties.uniprocessor_model (Prosa.Model.Processor.Ideal.processor_state Job)
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_Ideal_Schedule_ideal_proc_model_is_a_uniprocessor_model
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Model_Processor_PlatformProperties_uniprocessor_model_inst4 Job
         inst_3
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_3)
```
