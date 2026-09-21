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

- `Prosa/` is the official current Prosa v0.6 Lean translation candidate tree.
  It may contain declarations whose semantic-validation gate is still open.
- `Validation/` contains planning snapshots, scripts, certificates, fixtures,
  imported artifacts, and raw logs.
- `Reports/` contains human-readable current reports.

Historical Lean files, prototypes, validation fixtures, generated reports,
and compatibility declarations must not be copied into `Prosa/`. File
existence is not acceptance. The authoritative acceptance and coverage state
is recorded only in `Validation/planning/v06_pipeline/*status.json` and
`*manifest.json`; only declarations marked `ACCEPTED_V06_TRANSLATION` there
count as accepted production coverage.

## Planning baseline

The accepted dependency and mapping snapshots are under
`Validation/planning/v06_dependency/` and
`Validation/planning/v06_mapping/`. File-DAG order is authoritative for
translation readiness; the declaration DAG is a fine-grained aid and does not
prove independence from implicit instances or canonical/HB resolution.

The canonical file execution order is `v06_file_translation_order.md`. For
each step, the file DAG first determines which files are ready; the execution
order breaks ties among ready, unfinished files. A file is completed before
the next ready file is started, although a large file may use internal
semantic batches.

Human-readable translation history is maintained one report per authoritative
source file under
`Reports/files/<source-directory>/<first-report-timestamp>_<source-basename>.md`.
The timestamp is inherited from the earliest historical report that covered
the file, is written without a timezone suffix, and stays fixed as later work
is appended to the same canonical report. Reports under `Reports/legacy/` are
immutable historical evidence and are not the current file-status authority.
