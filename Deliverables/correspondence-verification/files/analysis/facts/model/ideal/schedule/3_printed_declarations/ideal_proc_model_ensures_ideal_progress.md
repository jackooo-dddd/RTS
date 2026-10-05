# `ideal_proc_model_ensures_ideal_progress`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.model.ideal.schedule.ideal_proc_model_ensures_ideal_progress`
- Lean: `Prosa.Analysis.Facts.Model.Ideal.Schedule.ideal_proc_model_ensures_ideal_progress`
- Certificate: `ideal_proc_model_ensures_ideal_progress_correspondence`

## Official Rocq

```coq
ideal_proc_model_ensures_ideal_progress :
forall {Job : JobType}, @ideal_progress_proc_model Job (ideal.processor_state Job)

ideal_proc_model_ensures_ideal_progress is not universe polymorphic
Arguments ideal_proc_model_ensures_ideal_progress {Job} j s _
ideal_proc_model_ensures_ideal_progress is opaque
Expands to: Constant prosa.analysis.facts.model.ideal.schedule.ideal_proc_model_ensures_ideal_progress
Declared in library prosa.analysis.facts.model.ideal.schedule, line 57, characters 8-47
@ideal_proc_model_ensures_ideal_progress
     : forall Job : JobType, @ideal_progress_proc_model Job (ideal.processor_state Job)
```

## Lean

```lean
Prosa.Analysis.Facts.Model.Ideal.Schedule.ideal_proc_model_ensures_ideal_progress : ∀ (Job : Prosa.Behavior.Job.JobType)
  [inst : DecidableEq Job],
  Prosa.Model.Processor.PlatformProperties.ideal_progress_proc_model (Prosa.Model.Processor.Ideal.processor_state Job)
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_Ideal_Schedule_ideal_proc_model_ensures_ideal_progress
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Model_Processor_PlatformProperties_ideal_progress_proc_model_inst4 Job
         inst_3
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_3)
```
