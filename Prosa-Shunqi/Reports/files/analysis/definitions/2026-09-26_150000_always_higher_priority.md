# analysis/definitions/always_higher_priority.v — canonical translation report

First experiment timestamp: **2026-09-26 15:00:00 +08:00**

## Authority and scope

- Official source: Prosa v0.6 commit `414e66760333eaa4ef78c685bcf53291c527a548`.
- Source file: `analysis/definitions/always_higher_priority.v`; layer 14; execution rank 97.
- Public declarations: **2** — `always_higher_priority` (Definition) and
  `always_higher_priority_jlfp` (Fact). Direct dependency `model/priority/classes.v` accepted.

## Translation

`Prosa/Analysis/Definitions/AlwaysHigherPriority.lean`:
`always_higher_priority j1 j2 := ∀ t, (hep_job_at t j1 j2 && !hep_job_at t j2 j1) = true`
under a `JLDP_policy`; the JLFP fact is stated under `[JLFP_policy Job]`, the
JLDP instance being the accepted `JLFP_to_JLDP` coercion instance (as in the
source). Proof: `⟨fun h => h 0, fun h _ => h⟩`. No Lean axioms.

## Validation

First run of the new spec-driven pipeline
`Validation/scripts/translation_file_pipeline.py` with
`Validation/tooling/file_specs/analysis_definitions_always_higher_priority.json`
(same prepare/check/publish gates as the per-file validators: hash-checked
dependency closure, byte-identical pinned source compiled with Rocq 9.3,
`Check @name` fingerprints `EXACT_HASH`, fresh Lean build, Lean axiom audit,
actual export — 4,913 lines — and Rocq import, certificate DAG, fail-closed
assumption audit, hash-chained publication).

- The first prepare failed in export because the pipeline did not pass
  `LEAN_PATH` to the export driver (the shell validators export it globally);
  fixed, run archived as `analysis_definitions_always_higher_priority_final_attempt1_export_env`.
- Certificates (`Validation/certificates/analysis_definitions_always_higher_priority/`):
  the accepted priority chain (`PcoBaseAdapter`, `PcoStaticOrder`, `PcoDynamicOrder`,
  `PriorityCoercionCorrespondence`) re-bound to `ImportedAlwaysHigherPriority`;
  `always_higher_priority_correspondence` (related JLDP policies ⇒ related
  propositions for all job pairs; instants covered both ways) and
  `always_higher_priority_jlfp_correspondence` (source: exact elaborated type
  via `type of`; target: imported theorem type; JLFP policies covered both
  ways; built with the accepted `JLFP_to_JLDP_correspondence`).
- Assumption audit: 5 certificates `CERTIFIED_WITH_PROP_SPROP_FOUNDATION`,
  `semantic_premises=[]`, no theorem dependency, no unexpected assumptions.

## Formal acceptance

`analysis_definitions_always_higher_priority_module_manifest.json` / `_status.json`:
coverage **96 / 357 files**, **708 / 2439 declarations**.

Current status: **ACCEPTED_V06_FILE**.
