# Prosa semantic-validation pilot

This directory is an isolated proof-of-concept validator for the modern Prosa
0.6 Lean translation. It does not touch `Prosa/Classic/` or modify the existing
Lean translation.

## Hardened Experiment 7 validator

The current trust-audited representative suite is run with:

```sh
REEXPORT=1 ./scripts/validate_experiment7_hardened.sh
```

This performs clean Lean compilation, actual-artifact export/import, Rocq
certificate compilation, automatic per-certificate assumption classification,
official-source elaborated-type fidelity checks, cache invalidation, and an
end-to-end interval-semantic mutation test. Its sole validation-defined axiom
is the isolated `PropSPropFoundation.interpret_strict`; equality and existential
forward transport are kernel-proved. See
`reports/2026-09-19_172311_HKT_validator_trust_and_rebuild_hardening_report.md`
and `reports/logs/experiment7/assumption_summary.json`.

The concrete Ideal `scheduled_in` certificate is `CERTIFIED`; the older
generic `ProcessorStateBridge.v` result remains relation-parametric as
described below.

Current `scheduled_in` outcome: **ACTUAL ARTIFACT IMPORTED; CORRESPONDENCE
CONDITIONAL**. The unchanged `ScheduledIn.out` now imports completely under
Rocq 9.3 with a minimally updated importer, and Rocq accepts
`scheduled_in_actual_artifact_bridge`, which directly mentions the imported
Lean declaration. The status is not yet `CERTIFIED`, because the core mapping
and `scheduled_on` preservation remain explicit representation-relation
premises. See `reports/2026-09-18_081300_HKT_scheduled_in_actual_artifact_import_report.md` for the exact
toolchain, patches, commands, assumption audit, and mutation result.

`ProcessorStateBridge.v` is now an actual-artifact correspondence theorem for
`scheduled_in`; it no longer uses the former handwritten Lean-side model.
`CompletedByCertificate.v` remains scaffolding and has not been connected to
an imported actual artifact.

Run the older scaffolding suite:

```sh
./scripts/verify.sh
```

Re-export from the unmodified Lean source after preparing Mathlib v4.33.1 and
the legacy-format `lean4export` commit documented in the report:

```sh
MATHLIB_DIR=/path/to/mathlib4-v4.33.1 \
LEAN4EXPORT=/path/to/lean4export \
./scripts/export_lean.sh
```

The generic import wrapper accepts any compatible built importer tree:

```sh
ROCQLI_SRC=/path/to/rocq-lean-import \
IMPORT_OPAM_SWITCH=validation-rocq-9.3 \
./scripts/import_lean.sh ImportedScheduled.v
```

Importer compatibility is version-sensitive; a successful command is required
before any actual-artifact semantic result can be claimed.

For the successful Rocq 9.3 `scheduled_in` pipeline, use the compatible
importer worktree and source tree recorded in the dated experiment report:

```sh
ROCQLI_SRC=/path/to/compatible/rocq-lean-import \
IMPORT_OPAM_SWITCH=rocq93rc1 \
PROSA_ROCQ_SRC=/path/to/compatible/prosa-v0.6-source \
./scripts/verify_scheduled_in_actual.sh
```

Set `REIMPORT=1` to re-import the unchanged `ScheduledIn.out` before compiling
the bridge, assumption audit, and polarity-mutation rejection fixture.
