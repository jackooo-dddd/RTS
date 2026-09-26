# model/preemption/fully_preemptive.v — canonical translation report

First experiment timestamp: **2026-09-28 02:00:00 +08:00**

## Authority and scope

- Prosa v0.6 `414e667…`; `model/preemption/fully_preemptive.v`; rank 131.
- Public declarations: **0**. The module re-exports `model/preemption/parameter.v` (accepted). It also declares, inside a section, `#[local] Instance fully_preemptive_job_model`: a named constant whose instance registration is section-local. Later source files enable it with `#[local] Existing Instance`, so it is not in the public inventory.

## Translation

`Prosa/Model/Preemption/FullyPreemptive.lean` imports `Prosa.Model.Preemption.Parameter`. It mirrors the constant as the plain Lean definition `fully_preemptive_job_model` (`job_preemptable _ _ = true`), which later translations enable locally in the same way.

## Validation

This uses the zero-declaration aggregation validator, extended fail-closed for this pattern. Besides its `Require Export` list, the source may contain only one section with `Context` lines and exactly the listed `#[local] Instance` items. The Lean aggregator may declare exactly the corresponding definitions and nothing else.

`model/preemption/parameter.v` was accepted through its extracted semantic source, so no pinned `.vo` exists. It is bound by a one-line shim at its logical path that re-exports the accepted `PreemptionParameterSemanticSource` module. The module's `.vo` hash is checked against the parameter manifest, and its `JobPreemptable` class is byte-identical.

The byte-identical official module compiles on this closure. The Lean aggregator and an aggregator-only interface probe (checked by `rfl`) compile with a clean axiom audit.

## Formal acceptance

Coverage **129 / 357 files**, **1020 / 2439 declarations**. Status: **ACCEPTED_V06_FILE**.
