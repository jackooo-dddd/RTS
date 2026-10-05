# `processor_state`

- Kind (Rocq): Inductive
- Rocq: `prosa.model.processor.spin.processor_state`
- Lean: `Prosa.Model.Processor.Spin.processor_state`
- Certificate: `spin_state_type_correspondence`

## Official Rocq

```coq
processor_state : JobType -> Type

processor_state is not universe polymorphic
Arguments processor_state Job
Expands to: Inductive prosa.model.processor.spin.processor_state
Declared in library prosa.model.processor.spin, line 17, characters 12-27
processor_state
     : JobType -> Type
```

## Lean

```lean
Prosa.Model.Processor.Spin.processor_state : Prosa.Behavior.Job.JobType → Type u_1
```

## Lean, imported into Rocq

```coq
Prosa_Model_Processor_Spin_processor_state
     : Prosa_Behavior_Job_JobType -> Type
```
