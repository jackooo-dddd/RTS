# `eps_is_uniproc`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.model.ideal_uni_exceed.eps_is_uniproc`
- Lean: `Prosa.Analysis.Facts.Model.IdealUniExceed.eps_is_uniproc`
- Certificate: `facts_uniprocessor_model_correspondence`

## Official Rocq

```coq
eps_is_uniproc : forall {Job : JobType}, @uniprocessor_model Job (ideal_uni_exceed.exceedance_proc_state Job)

eps_is_uniproc is not universe polymorphic
Arguments eps_is_uniproc {Job} j1 j2 s t _ _
eps_is_uniproc is opaque
Expands to: Constant prosa.analysis.facts.model.ideal_uni_exceed.eps_is_uniproc
Declared in library prosa.analysis.facts.model.ideal_uni_exceed, line 43, characters 8-22
@eps_is_uniproc
     : forall Job : JobType, @uniprocessor_model Job (ideal_uni_exceed.exceedance_proc_state Job)
```

## Lean

```lean
@Prosa.Analysis.Facts.Model.IdealUniExceed.eps_is_uniproc : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job],
  Prosa.Model.Processor.PlatformProperties.uniprocessor_model
    (Prosa.Model.Processor.IdealUniExceed.exceedance_proc_state Job)
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_IdealUniExceed_eps_is_uniproc
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Model_Processor_PlatformProperties_uniprocessor_model_inst4 Job
         inst_3
         (Prosa_Model_Processor_IdealUniExceed_exceedance_proc_state Job
            inst_3)
```
