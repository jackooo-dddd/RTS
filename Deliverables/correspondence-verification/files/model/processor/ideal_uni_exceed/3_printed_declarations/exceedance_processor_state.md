# `exceedance_processor_state`

- Kind (Rocq): Inductive
- Rocq: `prosa.model.processor.ideal_uni_exceed.exceedance_processor_state`
- Lean: `Prosa.Model.Processor.IdealUniExceed.exceedance_processor_state`
- Certificate: `iue_target_roundtrip`

## Official Rocq

```coq
exceedance_processor_state : JobType -> Type

exceedance_processor_state is not universe polymorphic
Arguments exceedance_processor_state {Job}
Expands to: Inductive prosa.model.processor.ideal_uni_exceed.exceedance_processor_state
Declared in library prosa.model.processor.ideal_uni_exceed, line 17, characters 12-38
@exceedance_processor_state
     : JobType -> Type
```

## Lean

```lean
Prosa.Model.Processor.IdealUniExceed.exceedance_processor_state : Prosa.Behavior.Job.JobType → Type u_1
```

## Lean, imported into Rocq

```coq
Prosa_Model_Processor_IdealUniExceed_exceedance_processor_state
     : Prosa_Behavior_Job_JobType -> Type
```
