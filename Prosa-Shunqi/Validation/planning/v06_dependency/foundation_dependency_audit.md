# Foundational Declaration Dependency Audit

Pinned source: Prosa v0.6 commit `414e66760333eaa4ef78c685bcf53291c527a548`.

Every entry below uses the elaborated Rocq type captured by `Check`, the official source command, and direct edges from the hardened graph. `UNRESOLVED_IMPLICIT_DEPENDENCY` means the explicit edge list is not claimed exhaustive.

## `prosa.behavior.job.JobType`

- Source: `behavior/job.v:7`; kind: `Definition`.
- Declaration layer: 0; confidence: `EXPLICIT_ONLY`.
- Implicit/canonical/HB risk: `UNRESOLVED_IMPLICIT_DEPENDENCY`.
- Direct internal dependencies: 0; generated-symbol-mapped edges: 0.

Elaborated Rocq type:

```text
JobType
     : Type
```

Official source declaration/body:

```coq
Definition JobType := eqType.
```

Direct extracted dependencies: none. This means no explicit/mapped internal edge was recovered; it does **not** prove independence from implicit resolution.

## `prosa.behavior.job.JobArrival`

- Source: `behavior/job.v:21`; kind: `Class`.
- Declaration layer: 1; confidence: `HIGH_EXPLICIT_AND_GENERATED`.
- Implicit/canonical/HB risk: `UNRESOLVED_IMPLICIT_DEPENDENCY`.
- Direct internal dependencies: 2; generated-symbol-mapped edges: 0.

Elaborated Rocq type:

```text
JobArrival
     : JobType -> Type
```

Official source declaration/body:

```coq
Class JobArrival (Job : JobType) := job_arrival : Job -> instant.
```

Direct extracted dependencies:

| Dependency | Edge kind | Region | Evidence | Generated symbol / mapping |
|---|---|---|---|---|
| `prosa.behavior.job.JobType` | STRUCTURE_FIELD_DEPENDENCY | TYPE_OR_STRUCTURE | ELABORATED_TYPE_CONFIRMED;EXPLICIT_GLOB_DEPENDENCY |  |
| `prosa.behavior.time.instant` | STRUCTURE_FIELD_DEPENDENCY | TYPE_OR_STRUCTURE | ELABORATED_TYPE_CONFIRMED;EXPLICIT_GLOB_DEPENDENCY |  |

## `prosa.behavior.job.JobCost`

- Source: `behavior/job.v:18`; kind: `Class`.
- Declaration layer: 1; confidence: `HIGH_EXPLICIT_AND_GENERATED`.
- Implicit/canonical/HB risk: `UNRESOLVED_IMPLICIT_DEPENDENCY`.
- Direct internal dependencies: 2; generated-symbol-mapped edges: 0.

Elaborated Rocq type:

```text
JobCost
     : JobType -> Type
```

Official source declaration/body:

```coq
Class JobCost (Job : JobType) := job_cost : Job -> work.
```

Direct extracted dependencies:

| Dependency | Edge kind | Region | Evidence | Generated symbol / mapping |
|---|---|---|---|---|
| `prosa.behavior.job.JobType` | STRUCTURE_FIELD_DEPENDENCY | TYPE_OR_STRUCTURE | ELABORATED_TYPE_CONFIRMED;EXPLICIT_GLOB_DEPENDENCY |  |
| `prosa.behavior.job.work` | STRUCTURE_FIELD_DEPENDENCY | TYPE_OR_STRUCTURE | ELABORATED_TYPE_CONFIRMED;EXPLICIT_GLOB_DEPENDENCY |  |

## `prosa.behavior.schedule.ProcessorState`

- Source: `behavior/schedule.v:22`; kind: `Class`.
- Declaration layer: 1; confidence: `HIGH_EXPLICIT_AND_GENERATED`.
- Implicit/canonical/HB risk: `UNRESOLVED_IMPLICIT_DEPENDENCY`.
- Direct internal dependencies: 2; generated-symbol-mapped edges: 0.

Elaborated Rocq type:

```text
ProcessorState
     : JobType -> Type
```

Official source declaration/body:

```coq
Class ProcessorState (Job : JobType) :=
  {
    State : Type;
    (** A [ProcessorState] instance provides a finite set of cores on which
        jobs can be scheduled. In the case of uniprocessors, this is irrelevant
        and may be ignored (by convention, the unit type is used as a
        placeholder in uniprocessor schedules, but this is not
        important). (Hint to the Coq novice: [finType] just means some type
        with finitely many values, i.e., it is possible to enumerate all cores
        of a multi-processor.)  *)
    Core : finType;
    (** For a given processor state and core, the [scheduled_on] predicate
        checks whether a given job is running on the given core. *)
    scheduled_on : Job -> State -> Core -> bool;
    (** For a given processor state and core, the [supply_on] function
        determines how much supply the core produces in the given
        state). *)
    supply_on : State -> Core -> work;
    (** For a given processor state and core, the [service_on]
        function determines how much service a given job receives on
        the given core). *)
    service_on : Job -> State -> Core -> work;
    (** We require [service_on] and [supply_on] to be consistent in
        the sense that a job cannot receive more service on a given
        core in a given state than there is supply on the core in this
        state. *)
    service_on_le_supply_on :
      forall j s r, service_on j s r <= supply_on s r;
    (** In addition, a job can receive service (on a given core) only
        if it is also scheduled (on that core). *)
    service_on_implies_scheduled_on :
      forall j s r, ~~ scheduled_on j s r -> service_on j s r = 0
  }.
```

Direct extracted dependencies:

| Dependency | Edge kind | Region | Evidence | Generated symbol / mapping |
|---|---|---|---|---|
| `prosa.behavior.job.JobType` | STRUCTURE_FIELD_DEPENDENCY | TYPE_OR_STRUCTURE | ELABORATED_TYPE_CONFIRMED;EXPLICIT_GLOB_DEPENDENCY |  |
| `prosa.behavior.job.work` | STRUCTURE_FIELD_DEPENDENCY | TYPE_OR_STRUCTURE | ELABORATED_TYPE_CONFIRMED;EXPLICIT_GLOB_DEPENDENCY |  |

## `prosa.behavior.schedule.scheduled_in`

- Source: `behavior/schedule.v:77`; kind: `Definition`.
- Declaration layer: 2; confidence: `HIGH_EXPLICIT_AND_GENERATED`.
- Implicit/canonical/HB risk: `UNRESOLVED_IMPLICIT_DEPENDENCY`.
- Direct internal dependencies: 1; generated-symbol-mapped edges: 1.

Elaborated Rocq type:

```text
@scheduled_in
     : forall (Job : JobType) (State0 : ProcessorState Job), Job -> State0 -> bool
```

Official source declaration/body:

```coq
Definition scheduled_in (j : Job) (s : State) : bool :=
    [exists c : Core, scheduled_on j s c].
```

Direct extracted dependencies:

| Dependency | Edge kind | Region | Evidence | Generated symbol / mapping |
|---|---|---|---|---|
| `prosa.behavior.schedule.ProcessorState` | BODY_DEPENDENCY | BODY | GENERATED_SYMBOL_MAPPED | prosa.behavior.schedule.Core;prosa.behavior.schedule.scheduled_on / SOURCE_DECLARATION_SPAN |

## `prosa.behavior.schedule.supply_in`

- Source: `behavior/schedule.v:82`; kind: `Definition`.
- Declaration layer: 2; confidence: `HIGH_EXPLICIT_AND_GENERATED`.
- Implicit/canonical/HB risk: `UNRESOLVED_IMPLICIT_DEPENDENCY`.
- Direct internal dependencies: 2; generated-symbol-mapped edges: 1.

Elaborated Rocq type:

```text
@supply_in
     : forall (Job : JobType) (State0 : ProcessorState Job), State0 -> work
```

Official source declaration/body:

```coq
Definition supply_in (s : State) : work :=
    \sum_(r : Core) supply_on s r.
```

Direct extracted dependencies:

| Dependency | Edge kind | Region | Evidence | Generated symbol / mapping |
|---|---|---|---|---|
| `prosa.behavior.job.work` | TYPE_DEPENDENCY | TYPE_OR_STRUCTURE | ELABORATED_TYPE_CONFIRMED;EXPLICIT_GLOB_DEPENDENCY |  |
| `prosa.behavior.schedule.ProcessorState` | BODY_DEPENDENCY | BODY | GENERATED_SYMBOL_MAPPED | prosa.behavior.schedule.Core;prosa.behavior.schedule.supply_on / SOURCE_DECLARATION_SPAN |

## `prosa.behavior.schedule.service_in`

- Source: `behavior/schedule.v:88`; kind: `Definition`.
- Declaration layer: 2; confidence: `HIGH_EXPLICIT_AND_GENERATED`.
- Implicit/canonical/HB risk: `UNRESOLVED_IMPLICIT_DEPENDENCY`.
- Direct internal dependencies: 2; generated-symbol-mapped edges: 1.

Elaborated Rocq type:

```text
@service_in
     : forall (Job : JobType) (State0 : ProcessorState Job), Job -> State0 -> work
```

Official source declaration/body:

```coq
Definition service_in (j : Job) (s : State) : work :=
    \sum_(r : Core) service_on j s r.
```

Direct extracted dependencies:

| Dependency | Edge kind | Region | Evidence | Generated symbol / mapping |
|---|---|---|---|---|
| `prosa.behavior.job.work` | TYPE_DEPENDENCY | TYPE_OR_STRUCTURE | ELABORATED_TYPE_CONFIRMED;EXPLICIT_GLOB_DEPENDENCY |  |
| `prosa.behavior.schedule.ProcessorState` | BODY_DEPENDENCY | BODY | GENERATED_SYMBOL_MAPPED | prosa.behavior.schedule.Core;prosa.behavior.schedule.service_on / SOURCE_DECLARATION_SPAN |

## `prosa.behavior.service.service_at`

- Source: `behavior/service.v:17`; kind: `Definition`.
- Declaration layer: 3; confidence: `EXPLICIT_ONLY`.
- Implicit/canonical/HB risk: `UNRESOLVED_IMPLICIT_DEPENDENCY`.
- Direct internal dependencies: 2; generated-symbol-mapped edges: 0.

Elaborated Rocq type:

```text
@service_at
     : forall (Job : JobType) (PState : ProcessorState Job), schedule PState -> Job -> instant -> work
```

Official source declaration/body:

```coq
Definition service_at (j : Job) (t : instant) := service_in j (sched t).
```

Direct extracted dependencies:

| Dependency | Edge kind | Region | Evidence | Generated symbol / mapping |
|---|---|---|---|---|
| `prosa.behavior.schedule.service_in` | BODY_DEPENDENCY | BODY | EXPLICIT_GLOB_DEPENDENCY |  |
| `prosa.behavior.time.instant` | TYPE_DEPENDENCY | TYPE_OR_STRUCTURE | ELABORATED_TYPE_CONFIRMED;EXPLICIT_GLOB_DEPENDENCY |  |

## `prosa.behavior.service.service_during`

- Source: `behavior/service.v:26`; kind: `Definition`.
- Declaration layer: 4; confidence: `EXPLICIT_ONLY`.
- Implicit/canonical/HB risk: `UNRESOLVED_IMPLICIT_DEPENDENCY`.
- Direct internal dependencies: 2; generated-symbol-mapped edges: 0.

Elaborated Rocq type:

```text
@service_during
     : forall (Job : JobType) (PState : ProcessorState Job), schedule PState -> Job -> instant -> instant -> nat
```

Official source declaration/body:

```coq
Definition service_during (j : Job) (t1 t2 : instant) :=
    \sum_(t1 <= t < t2) service_at j t.
```

Direct extracted dependencies:

| Dependency | Edge kind | Region | Evidence | Generated symbol / mapping |
|---|---|---|---|---|
| `prosa.behavior.service.service_at` | BODY_DEPENDENCY | BODY | EXPLICIT_GLOB_DEPENDENCY |  |
| `prosa.behavior.time.instant` | TYPE_DEPENDENCY | TYPE_OR_STRUCTURE | ELABORATED_TYPE_CONFIRMED;EXPLICIT_GLOB_DEPENDENCY |  |

## `prosa.behavior.service.service`

- Source: `behavior/service.v:31`; kind: `Definition`.
- Declaration layer: 5; confidence: `EXPLICIT_ONLY`.
- Implicit/canonical/HB risk: `UNRESOLVED_IMPLICIT_DEPENDENCY`.
- Direct internal dependencies: 2; generated-symbol-mapped edges: 0.

Elaborated Rocq type:

```text
@service
     : forall (Job : JobType) (PState : ProcessorState Job), schedule PState -> Job -> instant -> nat
```

Official source declaration/body:

```coq
Definition service (j : Job) (t : instant) := service_during j 0 t.
```

Direct extracted dependencies:

| Dependency | Edge kind | Region | Evidence | Generated symbol / mapping |
|---|---|---|---|---|
| `prosa.behavior.service.service_during` | BODY_DEPENDENCY | BODY | EXPLICIT_GLOB_DEPENDENCY |  |
| `prosa.behavior.time.instant` | TYPE_DEPENDENCY | TYPE_OR_STRUCTURE | ELABORATED_TYPE_CONFIRMED;EXPLICIT_GLOB_DEPENDENCY |  |

## `prosa.behavior.service.completed_by`

- Source: `behavior/service.v:43`; kind: `Definition`.
- Declaration layer: 6; confidence: `HIGH_EXPLICIT_AND_GENERATED`.
- Implicit/canonical/HB risk: `UNRESOLVED_IMPLICIT_DEPENDENCY`.
- Direct internal dependencies: 3; generated-symbol-mapped edges: 1.

Elaborated Rocq type:

```text
@completed_by
     : forall (Job : JobType) (PState : ProcessorState Job), schedule PState -> JobCost Job -> Job -> instant -> bool
```

Official source declaration/body:

```coq
Definition completed_by (j : Job) (t : instant) := service j t >= job_cost j.
```

Direct extracted dependencies:

| Dependency | Edge kind | Region | Evidence | Generated symbol / mapping |
|---|---|---|---|---|
| `prosa.behavior.job.JobCost` | BODY_DEPENDENCY | BODY | GENERATED_SYMBOL_MAPPED | prosa.behavior.job.job_cost / SOURCE_DECLARATION_SPAN |
| `prosa.behavior.service.service` | BODY_DEPENDENCY | BODY | EXPLICIT_GLOB_DEPENDENCY |  |
| `prosa.behavior.time.instant` | TYPE_DEPENDENCY | TYPE_OR_STRUCTURE | ELABORATED_TYPE_CONFIRMED;EXPLICIT_GLOB_DEPENDENCY |  |

## `prosa.behavior.service.completes_at`

- Source: `behavior/service.v:47`; kind: `Definition`.
- Declaration layer: 7; confidence: `EXPLICIT_ONLY`.
- Implicit/canonical/HB risk: `UNRESOLVED_IMPLICIT_DEPENDENCY`.
- Direct internal dependencies: 2; generated-symbol-mapped edges: 0.

Elaborated Rocq type:

```text
@completes_at
     : forall (Job : JobType) (PState : ProcessorState Job), schedule PState -> JobCost Job -> Job -> instant -> bool
```

Official source declaration/body:

```coq
Definition completes_at (j : Job) (t : instant) :=
    (~~ completed_by j t.-1 || (t == 0)) && completed_by j t.
```

Direct extracted dependencies:

| Dependency | Edge kind | Region | Evidence | Generated symbol / mapping |
|---|---|---|---|---|
| `prosa.behavior.service.completed_by` | BODY_DEPENDENCY | BODY | EXPLICIT_GLOB_DEPENDENCY |  |
| `prosa.behavior.time.instant` | TYPE_DEPENDENCY | TYPE_OR_STRUCTURE | ELABORATED_TYPE_CONFIRMED;EXPLICIT_GLOB_DEPENDENCY |  |

## `prosa.model.task.concept.TaskType`

- Source: `model/task/concept.v:10`; kind: `Definition`.
- Declaration layer: 0; confidence: `EXPLICIT_ONLY`.
- Implicit/canonical/HB risk: `UNRESOLVED_IMPLICIT_DEPENDENCY`.
- Direct internal dependencies: 0; generated-symbol-mapped edges: 0.

Elaborated Rocq type:

```text
TaskType
     : Type
```

Official source declaration/body:

```coq
Definition TaskType := eqType.
```

Direct extracted dependencies: none. This means no explicit/mapped internal edge was recovered; it does **not** prove independence from implicit resolution.

## `prosa.model.task.concept.JobTask`

- Source: `model/task/concept.v:19`; kind: `Class`.
- Declaration layer: 1; confidence: `HIGH_EXPLICIT_AND_GENERATED`.
- Implicit/canonical/HB risk: `UNRESOLVED_IMPLICIT_DEPENDENCY`.
- Direct internal dependencies: 2; generated-symbol-mapped edges: 0.

Elaborated Rocq type:

```text
JobTask
     : JobType -> TaskType -> Type
```

Official source declaration/body:

```coq
Class JobTask (Job : JobType) (Task : TaskType) := job_task : Job -> Task.
```

Direct extracted dependencies:

| Dependency | Edge kind | Region | Evidence | Generated symbol / mapping |
|---|---|---|---|---|
| `prosa.behavior.job.JobType` | STRUCTURE_FIELD_DEPENDENCY | TYPE_OR_STRUCTURE | ELABORATED_TYPE_CONFIRMED;EXPLICIT_GLOB_DEPENDENCY |  |
| `prosa.model.task.concept.TaskType` | STRUCTURE_FIELD_DEPENDENCY | TYPE_OR_STRUCTURE | ELABORATED_TYPE_CONFIRMED;EXPLICIT_GLOB_DEPENDENCY |  |
