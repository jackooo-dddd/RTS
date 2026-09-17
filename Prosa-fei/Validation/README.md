# Prosa semantic-validation pilot

This directory is an isolated proof-of-concept validator for the modern Prosa
0.6 Lean translation. It does not touch `Prosa/Classic/` or modify the existing
Lean translation.

Current outcome: **PIPELINE BLOCKED — ACTUAL LEAN ARTIFACT NOT IMPORTED**.
The real Lean declarations compile and export, but the available
Rocq/`rocq-lean-import` combinations stop in a transitive dependency before
either declaration is installed in Rocq. See `reports/pilot_report.md` for the
exact versions, failures, semantic mismatch, dependency graph, and commands.

The Rocq files are kernel-checked bridge scaffolding. In particular,
`ProcessorStateBridge.v` validates the minimal finite-existential argument on
the actual Rocq definition, and `CompletedByCertificate.v` validates the
composition rule while explicitly exposing `service_rel` and `cost_rel` as
uncertified inputs. Neither is an actual-artifact certificate.

Run the checked scaffolding and assumption audit:

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

Reproduce an import attempt with a built importer tree:

```sh
ROCQLI_SRC=/path/to/rocq-lean-import \
IMPORT_OPAM_SWITCH=validation-rocq-9.3 \
./scripts/import_lean.sh ImportedScheduled.v
```

An import command returning failure is currently expected and must not be
interpreted as semantic certification.
