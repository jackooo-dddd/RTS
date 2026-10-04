# Tool and gate changes (v0.6 family)

## 2026-10-04 — certifying a source-`Local` lemma, and amending an accepted file

**Why.** ProsaBuddy's benchmark task `train-15` is `job_arrival_is_bounded`, a `Local Lemma` of section `Case2` of
`analysis/abstract/restricted_supply/bounded_bi/jlfp.v`. The accepted translation (rank 302) had inlined it into
`busy_intervals_are_bounded_rs_jlfp`. The user decided (2026-10-04) to make it a Lean theorem of
`Prosa/Analysis/Abstract/RestrictedSupply/BoundedBi/Jlfp.lean` and re-validate that file. Two things were missing:
a way to certify a declaration that the authoritative inventory does not list (it lists public declarations only),
and a way to re-publish an already-accepted file without rewriting the publication chain built on it.

All changes are opt-in, and every existing gate still applies. Files that do not opt in behave exactly as before.

1. **Local-lemma type evidence (new script `scripts/elaborate_local_declaration_types.py`).**
   - It produces `Check @name` evidence for named source-`Local` lemmas, exactly as `elaborate_declaration_types.py`
     does for public ones: the same probe preamble (all main modules, same order), the same markers, normalization
     and hashing, on the official `prosa-0.6` switch over a build of the pinned tree.
   - `merge` checks that:
     - the source file has its inventoried sha256;
     - the name is a unique `Local` lemma of that file;
     - the name is absent from the authoritative inventory.
   - It writes the separate files `planning/v06_dependency/local_declaration_inventory.csv` and
     `local_declaration_type_evidence.json` (with provenance; logs in `planning/v06_dependency/logs/local_declarations/`).
   - `declaration_inventory.csv` and `declaration_type_evidence.json` are not modified.
2. **Pipeline spec key `local_declarations` (`translation_file_pipeline.py`).**
   - `inventory()` adds the listed local rows, ordered by source line. It requires each listed name to be recorded
     exactly once in the local inventory and not to clash with the authoritative one.
   - `type_evidence()` adds the local evidence only after checking that it is bound to its row (fingerprint and
     source file).
   - Extraction receives the merged evidence and `--local-declarations`. Everything downstream is unchanged:
     extraction checks, source-type gate, certificates, audits.
3. **Extractor flag `--local-declarations` (`extract_v06_semantic_source.py`).**
   - It extracts exactly the named `Local Lemma`/`Local Theorem` blocks: each must occur once and must not clash with
     a public block.
   - The statement header may then start with `Local`. Other blocks are unaffected.
4. **Pipeline spec key `amendment` (`translation_file_pipeline.py`).**
   - The run directory is `<slug><work_suffix>`, so the accepted run is untouched.
   - Publication requires that the accepted manifest and status still have the recorded sha256 values, and that
     every declaration they certified is certified again.
   - It writes `<slug>_module_<id>_{manifest,status}.json` and `imported/translation_order/<slug>__<id>/`. The
     manifest records the superseded records, the added declarations and the local declarations. The status has
     the per-file acceptance but no cumulative coverage: public-declaration coverage stays with the chain.
   - Existing manifests, statuses and the chain are not modified.
   - `update_reports_readme.py --check` still passes (357/357 files, 2439/2439 public declarations).
   - The final summary print of `publish` tolerates an amendment status (it has no `coverage` field).

**Not changed:** the escape gates, source-type gate, certificate checkpoints, Lean/Rocq axiom audits and the
assumption allowlists. The amendment's assumption configuration lists one more certificate and no new allowed
constant.

**Use.** `tooling/file_specs/analysis_abstract_restricted_supply_bounded_bi_jlfp__amend1.json`, published as
`analysis_abstract_restricted_supply_bounded_bi_jlfp_module_amendment1_*`. The amendment's statement probe
`fixtures/translation_order/BoundedBiJlfpAmend1StatementProbe.v` adds one display-only import, so that the classical
`busy_interval_prefix` prints unqualified as in the official environment.

**Backups (session scratchpad):** `x/translation_file_pipeline.pre_local_amend.py`,
`x/extract_v06_semantic_source.pre_local.py`, `x/Jlfp.pre_train15.lean`.
