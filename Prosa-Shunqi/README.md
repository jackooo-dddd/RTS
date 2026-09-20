# Prosa v0.6 → Lean 4 Translation

## Authority

- **Project:** Prosa v0.6 → Lean 4 translation
- **Authoritative Rocq source:** Prosa v0.6, commit
  `414e66760333eaa4ef78c685bcf53291c527a548`
- **Historical reference:** Prosa v0.4, commit
  `ee05f255e29676ad79e07b5d6cc59dc66cd7fcb7`
- **Historical Lean translation:** `../Prosa-fei/Prosa/` — **REFERENCE ONLY**
- **Target Lean:** 4.33.1 (`leanprover/lean4:v4.33.1`)
- **Target Mathlib:** `0df444a360eaa60ab8c11dca51a86af692955474`

Current Lean and Prosa v0.4 never override Prosa v0.6 semantics.

## Workspace layout

- `Prosa/` contains accepted production Prosa v0.6 translations only.
- `Validation/` contains planning snapshots, scripts, certificates, fixtures,
  imported artifacts, and raw logs.
- `Reports/` contains human-readable current reports.

The production tree starts empty. Historical Lean files, prototypes,
validation fixtures, generated reports, and compatibility declarations must
not be copied into `Prosa/`. A declaration enters production only through the
approved v0.6 migration and validation workflow.

## Planning baseline

The accepted dependency and mapping snapshots are under
`Validation/planning/v06_dependency/` and
`Validation/planning/v06_mapping/`. File-DAG order is authoritative for
translation readiness; the declaration DAG is a fine-grained aid and does not
prove independence from implicit instances or canonical/HB resolution.
