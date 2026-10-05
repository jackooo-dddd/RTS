# `InterferingWorkload`

- Kind (Rocq): Class
- Rocq: `prosa.analysis.abstract.definitions.InterferingWorkload`
- Lean: `Prosa.Analysis.Abstract.Definitions.InterferingWorkload`
- Certificate: `ad_workload_import_certificate`

## Official Rocq

```coq
InterferingWorkload : JobType -> Type

InterferingWorkload is not universe polymorphic
Arguments InterferingWorkload Job
InterferingWorkload is transparent
Expands to: Constant prosa.analysis.abstract.definitions.InterferingWorkload
Declared in library prosa.analysis.abstract.definitions, line 50, characters 0-97
InterferingWorkload
     : JobType -> Type
```

## Lean

```lean
Prosa.Analysis.Abstract.Definitions.InterferingWorkload : (Job : Prosa.Behavior.Job.JobType) →
  [DecidableEq Job] → Type u_1
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Abstract_Definitions_InterferingWorkload
     : forall Job : Prosa_Behavior_Job_JobType, DecidableEq Job -> Type
```
