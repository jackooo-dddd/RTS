# `rs_proc_model_is_a_uniprocessor_model`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.model.restricted_supply.schedule.rs_proc_model_is_a_uniprocessor_model`
- Lean: `Prosa.Analysis.Facts.Model.RestrictedSupply.Schedule.rs_proc_model_is_a_uniprocessor_model`
- Certificate: `facts_uniprocessor_model_correspondence`

## Official Rocq

```coq
rs_proc_model_is_a_uniprocessor_model :
forall {Job : JobType}, @uniprocessor_model Job (rs_processor_state Job)

rs_proc_model_is_a_uniprocessor_model is not universe polymorphic
Arguments rs_proc_model_is_a_uniprocessor_model {Job} j1 j2 s t _ _
rs_proc_model_is_a_uniprocessor_model is opaque
Expands to: Constant
            prosa.analysis.facts.model.restricted_supply.schedule.rs_proc_model_is_a_uniprocessor_model
Declared in library prosa.analysis.facts.model.restricted_supply.schedule, line 20, characters 8-45
@rs_proc_model_is_a_uniprocessor_model
     : forall Job : JobType, @uniprocessor_model Job (rs_processor_state Job)
```

## Lean

```lean
@Prosa.Analysis.Facts.Model.RestrictedSupply.Schedule.rs_proc_model_is_a_uniprocessor_model : ∀
  {Job : Prosa.Behavior.Job.JobType} [inst : DecidableEq Job],
  Prosa.Model.Processor.PlatformProperties.uniprocessor_model
    (Prosa.Model.Processor.RestrictedSupply.rs_processor_state Job)
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_RestrictedSupply_Schedule_rs_proc_model_is_a_uniprocessor_model
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : 
          DecidableEq Job),
       Prosa_Model_Processor_PlatformProperties_uniprocessor_model_inst4 Job
         inst_3
         (Prosa_Model_Processor_RestrictedSupply_rs_processor_state Job
            inst_3)
```
