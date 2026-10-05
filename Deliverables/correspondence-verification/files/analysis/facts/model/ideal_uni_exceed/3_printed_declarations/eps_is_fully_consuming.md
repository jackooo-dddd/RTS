# `eps_is_fully_consuming`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.model.ideal_uni_exceed.eps_is_fully_consuming`
- Lean: `Prosa.Analysis.Facts.Model.IdealUniExceed.eps_is_fully_consuming`
- Certificate: `facts_fully_consuming_model_correspondence`

## Official Rocq

```coq
eps_is_fully_consuming :
forall {Job : JobType}, @fully_consuming_proc_model Job (ideal_uni_exceed.exceedance_proc_state Job)

eps_is_fully_consuming is not universe polymorphic
Arguments eps_is_fully_consuming {Job} j s t _
eps_is_fully_consuming is opaque
Expands to: Constant prosa.analysis.facts.model.ideal_uni_exceed.eps_is_fully_consuming
Declared in library prosa.analysis.facts.model.ideal_uni_exceed, line 53, characters 8-30
@eps_is_fully_consuming
     : forall Job : JobType, @fully_consuming_proc_model Job (ideal_uni_exceed.exceedance_proc_state Job)
```

## Lean

```lean
@Prosa.Analysis.Facts.Model.IdealUniExceed.eps_is_fully_consuming : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job],
  Prosa.Model.Processor.PlatformProperties.fully_consuming_proc_model
    (Prosa.Model.Processor.IdealUniExceed.exceedance_proc_state Job)
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_IdealUniExceed_eps_is_fully_consuming
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Model_Processor_PlatformProperties_fully_consuming_proc_model_inst4 Job
         inst_3
         (Prosa_Model_Processor_IdealUniExceed_exceedance_proc_state Job
            inst_3)
```
