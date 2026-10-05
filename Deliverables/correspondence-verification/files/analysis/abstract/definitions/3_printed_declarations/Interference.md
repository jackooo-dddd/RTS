# `Interference`

- Kind (Rocq): Class
- Rocq: `prosa.analysis.abstract.definitions.Interference`
- Lean: `Prosa.Analysis.Abstract.Definitions.Interference`
- Certificate: `ad_interference_import_certificate`

## Official Rocq

```coq
Interference : JobType -> Type

Interference is not universe polymorphic
Arguments Interference Job
Interference is transparent
Expands to: Constant prosa.analysis.abstract.definitions.Interference
Declared in library prosa.analysis.abstract.definitions, line 33, characters 0-78
Interference
     : JobType -> Type
```

## Lean

```lean
Prosa.Analysis.Abstract.Definitions.Interference : (Job : Prosa.Behavior.Job.JobType) → [DecidableEq Job] → Type u_1
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Abstract_Definitions_Interference
     : forall Job : Prosa_Behavior_Job_JobType, DecidableEq Job -> Type
```
