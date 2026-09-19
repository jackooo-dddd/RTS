# Configuration-Driven Theorem Validation Pipeline Report — started 2026-09-19 09:31:16 HKT

## Progress log

### 2026-09-19 09:31:16 HKT — experiment resumed

- Baseline confirmed: experiment 4 already kernel-checks `scheduled_at_def` as `CERTIFIED_WITH_PROP_SPROP_BRIDGE` against the actual imported Lean artifact.
- Two prototype limitations remain in scope: a theorem-name-specific exporter branch and the handwritten `OriginalIdealScheduleSlice.v` source replay.
- Production files under `Prosa-fei/Prosa/` remain untouched.

### 2026-09-19 09:33:00 HKT — baseline inspection complete

- Confirmed the installed exporter still contains a hard-coded comparison against `Prosa.Analysis.Facts.Model.Ideal_schedule.scheduled_at_def`.
- Confirmed the official Prosa 0.6 source declarations are in `analysis/facts/model/ideal/schedule.v`, within `ScheduleClass`, with local Ideal processor-state instance and transparent `scheduled_in`/`scheduled_on`.
- Confirmed both target blocks (`scheduled_in_def`, `scheduled_at_def`) and their exact proof text are available in that official source.
- Selected source acquisition mode: `auto_extract`. Direct compilation of the full legacy file remains unsuitable on Rocq 9.3 because unrelated transitive legacy files fail; extraction will retain official declaration blocks verbatim and replace only the broad import prelude with the already-tested minimal compatibility imports.
- Found and corrected a malformed draft unified diff before applying it. This is not yet a validated exporter result.

### 2026-09-19 09:34:31 HKT — generic exporter compiled

- Replaced the theorem-name-specific patch with `lean4export-generic-statement-only.patch`.
- The exporter now reads exact theorem names from newline-separated `LEAN4EXPORT_STATEMENT_ONLY`; no Prosa declaration name occurs in the exporter patch.
- Applied the patch to a clean lean4export checkout and successfully rebuilt `lean4export` with Lean 4.33.1.

### 2026-09-19 09:36:07 HKT — official-source acquisition prototype passed Rocq

- Added a mapping-driven extractor. It reads the official Prosa 0.6 file, locates configured theorem blocks, recursively includes same-file proof dependencies (therefore `scheduled_at_def` brings in `scheduled_in_def`), and copies declaration blocks unchanged.
- Generated `rocq/GeneratedOfficialProsa06.v` from official source commit `414e66760333eaa4ef78c685bcf53291c527a548`.
- Compatibility transformation is limited to replacing legacy broad imports with `behavior.service` and `model.processor.ideal`; theorem statements and proofs are byte-derived from the official file.
- Source block SHA-256: `scheduled_in_def` = `4aed796a6e8d4e243ac2104f948e59d1ab5671cd87f04fe873a4dc830480d277`; `scheduled_at_def` = `c318449873f6ef84227c3aea69e92b504d1296c52c0cb538807abc8241c92c5a`.
- Normalized statement SHA-256: `scheduled_in_def` = `56eda467c77fe631cc939b99d1730f2eb74f7a852b54f377398280033d773966`; `scheduled_at_def` = `3f1c6b5b7ef8252f8f29538dbd11ebc1788e89eb60279a0ccc1b730fd62bc6b2`.
- Rocq 9.3 compiled the generated source. Kernel `Check` printed both exact theorem types, and `Print Assumptions` reported `Closed under the global context` for both.

### 2026-09-19 09:38:33 HKT — two configured Lean theorem statements exported

- `export_rts_validation.sh` now reads every `kind: theorem` / `lean_export_mode: statement_only` entry from `rts_validation_targets.yaml`, adds it to the export roots, and passes the complete name set through `LEAN4EXPORT_STATEMENT_ONLY`.
- A first run exposed and fixed a stale-build issue for the validation-only Ideal fixture; the script now compiles that fixture explicitly from `Validation/lean/IdealScheduledInFixture.lean`.
- Re-export then succeeded. Actual artifact: `export/RTSValidation.out`, 120,917 lines / 2,677,484 bytes, SHA-256 `60f07832ce3bdc4c8d940ead5afbfef94ed4600fabf65113bb4ebd31ee9d590b`.
- Artifact evidence shows both configured compiled names and both terminate in `#AX` statement records: namespace IDs `12261` (`scheduled_at_def`) and `12272` (`scheduled_in_def`). The exporter did not traverse either proof body; their type dependencies remain present.
- The manifest is `reports/logs/lean_statement_export_manifest.log`. No exporter source edit was needed when adding the second theorem.

### 2026-09-19 09:41:47 HKT — second theorem certificate passed

- Re-imported the regenerated actual Lean artifact with `rocq-lean-import` on Rocq 9.3+rc1.
- Added `scheduled_in_def_statement_certificate`, composed from the already-certified Ideal `scheduled_in`, the Ideal state/equality observation, imported Boolean equality, and the isolated Prop/SProp bridge.
- Added independent kernel witnesses tying each semantic proposition to (a) the actual imported Lean theorem constant and (b) the automatically generated official-source theorem constant. The correspondence proofs do not use either theorem proof to establish equivalence.
- `RTSTheoremCertificate.v` compiled successfully. Both theorem correspondence certificates have the same expected assumptions: importer foundations plus `prop_sprop_trusted_elim`. The actual-import statement witnesses additionally display the selected imported theorem `#AX`, as expected for statement-only export. Both official-source witnesses are closed under the global context.
- Deleted the handwritten `OriginalIdealScheduleSlice.v`; it is no longer part of the driver.

### 2026-09-19 09:45:31 HKT — final clean end-to-end run passed

Command executed:

```bash
REEXPORT=1 Validation/scripts/validate_rts_translation.sh
```

The run rebuilt the generic exporter, derived Lean modules and theorem names from the mapping, exported the actual compiled Lean declarations, imported the artifact into Rocq, regenerated and compiled the official-source slice, compiled reusable bridges and both semantic certificates, audited forbidden proof escapes, ran `Print Assumptions`, and reran the existing mutation rejection.

Final result: **16 / 16 selected declarations validated**. In particular:

| Theorem target | Actual Lean imported | Official source automatic | Correspondence | Source assumptions | Status |
| --- | --- | --- | --- | --- | --- |
| `scheduled_in_def` | yes | yes | pass | closed | `CERTIFIED_WITH_PROP_SPROP_BRIDGE` |
| `scheduled_at_def` | yes | yes | pass | closed | `CERTIFIED_WITH_PROP_SPROP_BRIDGE` |

Artifact SHA-256: `60f07832ce3bdc4c8d940ead5afbfef94ed4600fabf65113bb4ebd31ee9d590b`.

## Final pipeline design

### Configuration

`mapping/rts_validation_targets.yaml` is the source of theorem target names, source paths, acquisition mode, source commit/hash, Lean source/module, import name, certificate, dependencies, assumptions, and status. The two theorem records use `lean_export_mode: statement_only` and `source_acquisition.mode: auto_extract`.

### Generic Lean statement export

`patches/lean4export-generic-statement-only.patch` contains no Prosa symbol. It reads `LEAN4EXPORT_STATEMENT_ONLY` and emits `#AX` for exactly those theorem declarations after recursively exporting their compiled types. All unselected definitions/theorems retain the normal body-export behavior. `export_rts_validation.sh` derives both the theorem names and containing Lean modules from the mapping, so adding another theorem does not require editing exporter source.

### Official Rocq source acquisition and fidelity

`scripts/extract_rocq_declarations.py` reads official Prosa 0.6 source, extracts the configured declaration blocks, and automatically includes earlier same-file declarations referenced by their proof text. It enforces the configured block SHA-256 before producing `rocq/GeneratedOfficialProsa06.v` and records normalized statement hashes in `reports/logs/source_fidelity.json`.

The sole compatibility transformation is replacing the original file's broad legacy import prelude with the minimal Rocq-9.3-buildable imports. The declaration statement and proof blocks are not transformed. Rocq then `Check`s the generated declarations and `Print Assumptions` reports both source theorems closed under the global context. This combines byte-level provenance checking with kernel-level type checking; it is not merely a string comparison.

Source provenance:

- File: `analysis/facts/model/ideal/schedule.v`
- Prosa release: 0.6
- Recorded source commit: `414e66760333eaa4ef78c685bcf53291c527a548`
- `scheduled_in_def` block SHA-256: `4aed796a6e8d4e243ac2104f948e59d1ab5671cd87f04fe873a4dc830480d277`
- `scheduled_at_def` block SHA-256: `c318449873f6ef84227c3aea69e92b504d1296c52c0cb538807abc8241c92c5a`

### Semantic and trust boundary

The two correspondences are bidirectional `PropSPropRel` statements. They are derived compositionally from actual-artifact definition certificates and Boolean equality preservation, not from the original or translated theorem proof. The single explicit non-importer trust boundary is:

```text
prop_sprop_trusted_elim : forall P : Prop, StrictlyInhabited P -> P
```

It appears in `Print Assumptions`; therefore theorem results are deliberately labeled `CERTIFIED_WITH_PROP_SPROP_BRIDGE`, not axiom-free `CERTIFIED`.

## Answers to the research questions

1. **Is theorem statement-only export generic?** Yes. Selection is an environment-configured set populated from the mapping; the patch has no theorem-specific branch.
2. **Does adding a theorem require exporter changes?** No. For another theorem in a mapped Lean module, add its mapping entry; modules and names are derived automatically.
3. **Do source declarations come from official Prosa 0.6?** Yes, via automatic extraction from the pinned official source tree, not handwritten replay.
4. **How is an extracted statement protected?** The complete declaration block is copied unchanged, checked against its configured SHA-256, assigned a normalized statement hash, compiled by Rocq, and tied to the certificate proposition by an exact-type witness.
5. **Did two real theorems use the same pipeline?** Yes: `scheduled_in_def` and `scheduled_at_def` both passed export, import, source acquisition, correspondence proof, and assumption audit through one driver.
6. **What changes for a third theorem?** For another theorem in this official source file: add one mapping record and its semantic certificate in the shared certificate module. No exporter, extractor, import driver, or source slice edit is required. Semantic proof construction is intentionally not faked or inferred from names.
7. **Is it ready for batch expansion?** Yes for theorem targets in the currently supported source-file pattern, and the Lean-side module/name selection is already generic. The extractor currently emits one generated module for one Rocq source-file group per run; supporting batches spanning multiple official Rocq files is the next engineering extension, not a semantic blocker.

## Reproduction and evidence

```bash
cd Prosa-fei
REEXPORT=1 Validation/scripts/validate_rts_translation.sh
```

Key evidence files:

- `reports/logs/final_theorem_pipeline_summary.log`
- `reports/logs/lean_statement_export_manifest.log`
- `reports/logs/source_fidelity.json`
- `reports/logs/import_rts_canonical_rocq93.log`
- `reports/logs/validate_GeneratedOfficialProsa06.log`
- `reports/logs/validate_RTSTheoremCertificate.log`

No production Lean file under `Prosa-fei/Prosa/` was modified.
