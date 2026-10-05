# `processor_state`

- Kind (Rocq): Inductive
- Rocq: `prosa.model.processor.varspeed.processor_state`
- Lean: `Prosa.Model.Processor.Varspeed.processor_state`
- Certificate: `vs_state_type_correspondence`

## Official Rocq

```coq
processor_state : JobType -> Type

processor_state is not universe polymorphic
Arguments processor_state Job
Expands to: Inductive prosa.model.processor.varspeed.processor_state
Declared in library prosa.model.processor.varspeed, line 20, characters 12-27
processor_state
     : JobType -> Type
```

## Lean

```lean
Prosa.Model.Processor.Varspeed.processor_state : Prosa.Behavior.Job.JobType → Type u_1
```

## Lean, imported into Rocq

```coq
Prosa_Model_Processor_Varspeed_processor_state
     : Prosa_Behavior_Job_JobType -> Type
```
