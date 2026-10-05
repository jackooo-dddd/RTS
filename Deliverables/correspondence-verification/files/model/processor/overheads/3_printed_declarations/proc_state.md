# `proc_state`

- Kind (Rocq): Inductive
- Rocq: `prosa.model.processor.overheads.proc_state`
- Lean: `Prosa.Model.Processor.Overheads.proc_state`
- Certificate: `ovh_state_target_roundtrip`

## Official Rocq

```coq
proc_state : JobType -> Type

proc_state is not universe polymorphic
Arguments proc_state Job
Expands to: Inductive prosa.model.processor.overheads.proc_state
Declared in library prosa.model.processor.overheads, line 23, characters 12-22
proc_state
     : JobType -> Type
```

## Lean

```lean
Prosa.Model.Processor.Overheads.proc_state : Prosa.Behavior.Job.JobType → Type u_1
```

## Lean, imported into Rocq

```coq
Prosa_Model_Processor_Overheads_proc_state
     : Prosa_Behavior_Job_JobType -> Type
```
