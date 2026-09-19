# Validator Trust and Rebuild Hardening Report

**Experiment:** 7  
**Start:** 2026-09-19 17:23:11 HKT  
**Frozen repository commit:** `1eb820d349364ced61a2ddc2de63823dd3d7b472`  
**Constraint:** no modification under `Prosa-fei/Prosa/`.

## Progress log

### 2026-09-19 17:23:11 HKT — initial audit

- Confirmed the production translation is clean and outside the modification scope.
- Existing `PropSPropBridge.v` contains three axioms: backward interpretation `prop_sprop_trusted_elim`, forward existential transport `prop_sprop_trusted_exists_intro`, and forward equality transport `prop_sprop_trusted_eq_intro`.
- Located a kernel-defined equality conversion already used by `HardCoreCertificates.v`: `hard_coq_eq_to_imported_eq`. This demonstrates that the equality forward axiom is unnecessary and should be replaced by a reusable kernel proof.
- Confirmed current validation scripts still use fixed status `echo` output and that `export_hard_validation.sh` skips compilation whenever an `.olean` already exists. Both require hardening.
- No Experiment 7 status changes are claimed at this timestamp.

### 2026-09-19 17:27:05 HKT — forward axioms eliminated

- Added the formal `PropSPropFoundation.v`; `PropSPropBridge.v` is now only a compatibility re-export.
- Replaced `prop_sprop_trusted_eq_intro` with kernel-defined `coq_eq_to_imported_eq`, abstracted from the previously local proof in `HardCoreCertificates.v`.
- Ran an independent Rocq 9.3 probe for `exists x, P x -> StrictlyExists A P`. Contrary to the previous assumption, the kernel accepts the direct match. Replaced `prop_sprop_trusted_exists_intro` with kernel-defined `embed_exists`.
- `Print Assumptions` confirms that `embed_prop`, `embed_exists`, `coq_eq_to_imported_eq`, and equality conversions add no axioms beyond the importer's definitional-UIP declaration for imported equality.
- The sole remaining validator axiom is now `interpret_strict : forall P, StrictlyInhabited P -> P`, the general `SProp -> Prop` interpretation direction.
- Probe and foundation logs are isolated under `reports/logs/experiment7/`.

### 2026-09-19 17:40:03 HKT — fresh-build and automated-audit milestones

- Reworked the hard-target exporter to compile in a fresh, uniquely named Lean build directory instead of accepting a pre-existing `.olean` from an earlier run. Its manifest records the Lean toolchain, repository/source hashes, build directory, and exported artifact SHA-256.
- Added a validation-only cache-invalidation test. It compiled two source fixtures differing only in the compiled value (`0` versus `1`) in separate fresh build directories and exported both actual artifacts. Their SHA-256 values differ (`244b8d...d6f4` versus `d7fa40...ea87`), so the test passed.
- Added a marker-based `Print Assumptions` audit and allowlist classifier. Status is now derived independently for each certificate; ordinary quantified inputs are not classified as unresolved semantic premises.
- Current classification has no target-theorem self-dependency, unexpected axiom, or validation-specific semantic premise. `scheduled_at_def`, `nin_rem_all`, `exists_first_intermediate_point`, `big_nat_eq0`, `sum_of_ones`, and `sum_le_summation_range` depend on the single foundation principle `interpret_strict`; `rem_all`, the three spin constructors, and `spin_scheduled_on` are foundation-free.
- Added a validation-only, actual-artifact mutation pipeline for interval sums. It freshly compiles and exports Lean `Finset.Ico` (original), `Finset.Icc` (mutant), and a semantics-preserving helper-refactoring control, imports those artifacts into Rocq, and kernel-checks the counterexample `m = n = 0`, `F 0 = 1`: the source/`Ico` sum is `0`, while the `Icc` mutant is `1`. The negative mutation is detected and the general positive control is accepted.
- Evidence: `reports/logs/experiment7/cache_invalidation_test.log`, `assumption_summary.json`, `interval_mutation_export.log`, `interval_mutation_import.log`, and `interval_mutation_certificate.log`.

### 2026-09-19 17:44:23 HKT — elaborated source-fidelity audit passes

- Added `scripts/audit_source_fidelity.py`. For each auto-extracted target it verifies the pinned official block hash, byte identity of that block in the generated module, reconstructed `Section`/`Context` commands, and absence of omitted local instance/transparent setup.
- The audit obtains the official fully explicit declaration type from the installed, kernel-checked Prosa 0.6 module using its native Rocq 9.0.1 environment. It independently obtains the generated module's fully explicit type under the Rocq 9.3 validation environment using `Set Printing All; Check @declaration`.
- Types must be textually identical after only erasing the generated module qualifier on byte-identically copied local dependencies (for example, `Generated_util__list.rem_all` versus official `rem_all`). This comparison retains implicit parameters, resolved instances, binders, notation elaboration, and the rest of the fully elaborated term.
- All six auto-extracted representative targets pass: `big_nat_eq0`, `sum_of_ones`, `sum_le_summation_range`, `rem_all`, `nin_rem_all`, and `exists_first_intermediate_point`.
- Any hash, context, local-setup, compilation, or elaborated-type mismatch is now classified `BLOCKED_BY_SOURCE_EXTRACTION` and makes the audit command fail.
- Evidence: `reports/logs/experiment7/source_fidelity_audit.json` and `source_fidelity_audit.log`.

### 2026-09-19 17:54:38 HKT — fresh rebuild exposed and fixed a hidden dependency

- The first full `REEXPORT=1` run successfully rebuilt/exported all hard targets from fresh directories, then failed while rebuilding the RTS artifact because the old RTS exporter had implicitly relied on cached `.olean` files for non-theorem modules.
- Concrete error: the fresh fixture build could not find `Prosa/Model/Processor/Ideal.olean`; the module-list query also revealed older mapping entries without `lean_source_file`.
- This is a useful successful invalidation test rather than a semantic failure. Added a configuration-level `lean_modules` list to `rts_validation_targets.yaml` and taught the mapping reader to combine it with per-target source modules. No production source was changed.
- The full clean pipeline is being rerun from the frozen source snapshot after this fix; no final status is claimed from the failed run.

### 2026-09-19 18:00:53 HKT — full clean pipeline passes

The mapping-driven command below completed successfully from the frozen production snapshot:

```bash
cd Prosa-fei
REEXPORT=1 ./Validation/scripts/validate_experiment7_hardened.sh
```

It performed fresh Lean compilation, actual-artifact export/import, source acquisition/fidelity checks, Rocq certificate compilation, per-certificate assumption auditing, cache invalidation, and the end-to-end semantic mutation test.

#### Machine-checked representative results

| Target/certificate | Status determined by audit | Validation-specific semantic premise | Target imported theorem used as proof assumption? |
| --- | --- | --- | --- |
| `scheduled_at_def` | `CERTIFIED_WITH_PROP_SPROP_FOUNDATION` | none | no |
| `rem_all` | `CERTIFIED` | none | no |
| `nin_rem_all` | `CERTIFIED_WITH_PROP_SPROP_FOUNDATION` | none | no |
| `exists_first_intermediate_point` | `CERTIFIED_WITH_PROP_SPROP_FOUNDATION` | none | no |
| `big_nat_eq0` | `CERTIFIED_WITH_PROP_SPROP_FOUNDATION_AND_STATEMENT_EXPORT` | none | no |
| `sum_of_ones` | `CERTIFIED_WITH_PROP_SPROP_FOUNDATION_AND_STATEMENT_EXPORT` | none | no |
| `sum_le_summation_range` | `CERTIFIED_WITH_PROP_SPROP_FOUNDATION_AND_STATEMENT_EXPORT` | none | no |
| `spin.processor_state.Idle` | `CERTIFIED` | none | n/a |
| `spin.processor_state.Spin` | `CERTIFIED` | none | n/a |
| `spin.processor_state.Progress` | `CERTIFIED` | none | n/a |
| `spin_scheduled_on` | `CERTIFIED` | none | n/a |

`sum_diff`, `sum_seq_gt0P`, and `sum_pred_diff` are now `SOURCE_UNMAPPED`, not `FAILED`: no declaration with those names exists in the pinned official Prosa 0.6 source. No semantic mismatch was established for them.

#### Minimal Prop/SProp foundation

`PropSPropFoundation.v` is now the sole entry point used by theorem-level certificates.

Kernel-proved components:

- ordinary `Prop` truth embedding into `SProp` (`embed_prop`);
- existential/witness transport from `exists x, P x` to `StrictlyExists A P` (`embed_exists`);
- Rocq equality to imported Lean equality (`coq_eq_to_imported_eq`);
- imported equality back to Rocq equality and strict equality witnesses;
- reusable `PropSPropRel` construction and theorem-level combinators.

Axiomatic core:

- exactly one declaration, `interpret_strict : forall P : Prop, StrictlyInhabited P -> P`.

The old forward axioms `prop_sprop_trusted_exists_intro` and `prop_sprop_trusted_eq_intro` were deleted. The old `prop_sprop_trusted_elim` name is also gone; its unavoidable role is isolated under the foundation API. A real negative Rocq 9.3 experiment reports:

```text
Incorrect elimination ... return type has sort "Prop" while it should be SProp.
... strict proofs can be eliminated only to build strict proofs.
```

Thus the remaining axiom is not retained due to tactic inconvenience; it represents the prohibited general elimination from `SProp` into `Prop`. The one-command validator checks that this is the only `Axiom` anywhere in the validation Rocq sources.

#### Automatic assumption classification

`classify_assumptions.py` consumes marked `Print Assumptions` output for each certificate and separates:

- `PropSPropFoundation.interpret_strict`;
- importer primitives and definitional UIP;
- statement-only Lean dependencies;
- target-theorem self-dependency;
- named validation-specific semantic premises;
- unexpected assumptions.

An unexpected item or target-theorem self-dependency fails the validator. A real semantic premise yields `CONDITIONAL`. Ordinary universally quantified inputs and relation parameters are not treated as unresolved premises. The three finite-sum theorem certificates explicitly carry the additional statement-export boundary because their large imported transitive Lean theorem dependencies were exported by type only; this boundary is no longer hidden under “importer foundation.”

#### Fresh-build guarantee

Both `export_hard_validation.sh` and `export_rts_validation.sh` now allocate fresh build directories by default. The prior `[[ -f "$output" ]]` check only deduplicates recursive imports inside that newly created directory; it cannot reuse an earlier run's `.olean`. Manifests record:

- repository commit `1eb820d349364ced61a2ddc2de63823dd3d7b472`;
- Lean toolchain `leanprover/lean4:v4.33.1`;
- production Lean tree hash `7426e874bd049e6f007b2695ef13f7209a0a1f8f`;
- exact temporary build directory;
- compiled source hashes;
- export artifact SHA-256.

The cache fixture test changed compiled Lean value `0` to `1`; fresh export hashes changed from `244b8d...d6f4` to `d7fa40...ea87`. The clean RTS run also exposed a formerly hidden cached-module dependency, which was repaired with an explicit configuration-level module closure.

Final representative artifact hashes:

- `HardCoreValidation.out`: `b546b2257e12872d159afcdc1f4c6e64ae7678d7b5e4ea93bd73ad2400142b96`
- `ExistsFirstIntermediatePoint.out`: `c3fb77511b70d968523d5e4ae51f3a1b7df26edf47f998a7a11fcfc32ccfe78c`
- `BigNatEq0AllStatements.out`: `2a9402d7202356eaed09c22553a776f2ea16ab5928567d5d62b4e218895518ab`
- `RTSValidation.out`: `60f07832ce3bdc4c8d940ead5afbfef94ed4600fabf65113bb4ebd31ee9d590b`
- mutation artifact: `4a9e6616fa7deb2ff6853c9372ee0418f91e834575c9d190ba7969d925406401`

#### Mutation strength

The negative control is a real independently compiled/exported/imported Lean artifact using `Finset.Icc` instead of `Finset.Ico`. Rocq computes the concrete counterexample `m = n = 0`, `F 0 = 1`: official/`Ico` is `0`, mutant/`Icc` is `1`, and the semantic match is rejected. A general positive control that only factors the original `Ico` computation through a helper is accepted.

#### Source fidelity

For all six hard auto-extracted targets and both ideal-schedule theorems, the audit now checks:

1. pinned source commit and configured source-block SHA-256;
2. byte-identical declaration block in the generated file;
3. reconstructed active contexts and local setup;
4. the official declaration's fully explicit type from the installed Prosa 0.6 `.vo` under Rocq 9.0.1;
5. the extracted declaration's fully explicit type independently elaborated under Rocq 9.3;
6. equality after only documented module-qualification normalization.

This catches missing implicit arguments, contexts, instances, and notation elaboration changes. Failure is `BLOCKED_BY_SOURCE_EXTRACTION`, never a silent approximation.

#### Final TCB and explicit boundaries

The result trusts:

- the Lean kernel that produced the fresh `.olean` files;
- `lean4export` plus the generic statement-only export mode;
- `rocq-lean-import` and its imported primitives/definitional-UIP representation;
- the Rocq 9.3 kernel;
- the single isolated `interpret_strict` axiom for theorem directions that eliminate strict propositions to ordinary `Prop`;
- for the three finite-sum theorem certificates only, the explicitly enumerated statement-only transitive Lean theorem dependencies.

It does **not** trust an LLM semantic judgment, a handwritten Lean-side Rocq model, the target imported theorem as the certificate proof, the removed equality/existential forward axioms, or stale `.olean` files.

#### Evidence and reproduction

Primary evidence is under `Validation/reports/logs/experiment7/`:

- `assumption_summary.json` and `assumption_statuses.log`;
- `source_fidelity_audit.json` and `source_fidelity_rts_audit.json`;
- `cache_invalidation_test.log`;
- `interval_mutation_*` logs;
- `sprop_to_prop_actual_error.log`;
- fresh Lean export manifests and per-certificate Rocq logs.

No file under `Prosa-fei/Prosa/` was modified.

### 2026-09-19 18:04:15 HKT — final entry-point verification

- `bash -n` passed for all new/modified shell entry points.
- Python byte-compilation passed for the extractor, source-fidelity auditor, and assumption classifier.
- `git diff --check` passed.
- The finalized command was rerun with `REEXPORT=0`; this intentionally reused the artifacts produced by the immediately preceding successful clean `REEXPORT=1` run while repeating import, source-fidelity, mutation, certificate compilation, and assumption classification. It exited `0` with the statuses in the table above.
- A final production-tree check reported no changes under `Prosa-fei/Prosa/`.
- A final Rocq-source scan found exactly one `Axiom`: `PropSPropFoundation.interpret_strict`.
