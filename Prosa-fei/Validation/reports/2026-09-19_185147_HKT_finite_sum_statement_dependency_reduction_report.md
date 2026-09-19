# Finite-Sum Statement Dependency Reduction Report

**Experiment:** 8/9 (statement-dependency reduction and semantic-graph decoupling)  
**Start:** 2026-09-19 18:51:47 HKT  
**Frozen repository commit:** `b6becfb7c6cb8317469b0be50e91c9153edf7c87`  
**Frozen production-tree object:** `7426e874bd049e6f007b2695ef13f7209a0a1f8f`  
**Constraint:** no modification under `Prosa-fei/Prosa/`.

## Progress log

### 2026-09-19 18:51:47 HKT — baseline captured

- Loaded the actual Experiment 7 `Print Assumptions` classification from `reports/logs/experiment7/assumption_summary.json`.
- Each of `big_nat_eq0`, `sum_of_ones`, and `sum_le_summation_range` has 43 statement-only transitive dependencies. The unique union is also 43 because all three use the same actual imported `Finset.Ico`/`Finset.sum` computation path.
- The export artifact contains 44 `#AX` declarations: those 43 dependencies plus the selected target theorem `Prosa.Util.Sum.big_nat_eq0`. The semantic certificate does not depend on the target theorem itself.
- Inspection shows that these assumptions are introduced through the actual imported interval-sum representation and its typeclass/proof fields, not by explicit uses of the corresponding theorem names in the Rocq bridge proof.
- Experiment 8 will therefore test selective proof-body export for small arithmetic dependencies while retaining statement-only export for the target theorem and harder representation-only dependencies. This preserves the existing structural source↔target semantic proof.

### 2026-09-19 19:27:34 HKT — Experiment 9 target-type normalization works for two targets

- Added a generic exporter mode that takes an actual compiled theorem type, applies Lean meta-level reduction, and accepts the normalized type only after Lean reports it definitionally equal to the original type. This does not inspect or export the theorem proof body.
- For `big_nat_eq0`, the actual compiled type normalized from the `Finset.Ico`/`Finset.sum` presentation to `List.range'` + `List.map` + `List.foldr`; the exporter logged `defeq=true`, original hash `3868918011`, normalized hash `2254104721`, and constant count `15 -> 14`.
- For `sum_of_ones`, the exporter logged `defeq=true`, original hash `406666510`, normalized hash `2639695887`, and constant count `12 -> 8`.
- The fresh artifact `export/FiniteNatSumNormalizedSimpleTargets.out` has SHA-256 `31423b3a4c8ddfb6bf3e10ae6ed0deadd1ce5eb4a770847da306eda44d86a274`. It contains exactly the two selected target theorem declarations as `#AX` signatures and zero transitive statement-only theorem exports.
- `ImportedFiniteNatSumNormalized93.v`, `HardSumCertificate.v`, and `FiniteNatSumBridge.v` compile against this artifact. The finite-sum bridge continues to prove the correspondence by structural computation over imported `List.range'`, `List.map`, and `List.foldr` bodies.
- The normalized `sum_of_ones` target type is now matched exactly in `FiniteNatSumReuseCertificates.v`. Rocq progressed through its target witness and printed assumptions for `sum_of_ones_statement_certificate`: only importer equality (`eq relies on definitional UIP`) and `PropSPropFoundation.interpret_strict` remain. None of the previous 43 transitive Lean theorem signatures appears.
- `sum_le_summation_range` does not benefit from `reduceAll`: its target type retains `Finset.Ico`, `Finset.sum`, locally-finite-order instances, and proof fields. It is therefore temporarily kept on the selectively reduced old artifact (SHA-256 `91c378069cd2aa1f28d291fb23656fe571186788ffe9ae450bc97fd183eaa20e`) while the two normalized targets use the smaller artifact.
- Current blocker is engineering isolation, not a semantic mismatch: importing the old and normalized artifacts in one Rocq module gives distinct module-qualified copies of `List` computation constants. The old fallback bridge is being isolated/adapted so its representation cannot contaminate the normalized certificates.

### 2026-09-19 19:31:36 HKT — all three certificates compile; automatic audit confirms the reduction

- Adapted the old Finset fallback bridge with module-qualified old-artifact `List.range'`, `List.map`, `List.foldr`, and `Nat.sub` computation lemmas. These lemmas are proved by Rocq reduction and induction; no new axiom or semantic premise was introduced.
- `FiniteNatSumReuseCertificates.v` now compiles successfully with both representations kept explicit: normalized list computation for `sum_of_ones`, old Finset computation only for `sum_le_summation_range`.
- Added `AssumptionAuditFiniteSumExperiment9.v` and a separate classifier configuration. The automatic results are:
  - `big_nat_eq0`: `CERTIFIED_WITH_PROP_SPROP_FOUNDATION`, zero transitive statement-only dependencies.
  - `sum_of_ones`: `CERTIFIED_WITH_PROP_SPROP_FOUNDATION`, zero transitive statement-only dependencies.
  - `sum_le_summation_range`: `CERTIFIED_WITH_PROP_SPROP_FOUNDATION_AND_STATEMENT_EXPORT`, 39 transitive statement-only dependencies.
- All three have `semantic_premises = []`, `target_theorem_dependency = false`, and `unexpected = []`. The target theorem signatures are retained as provenance witnesses but are not used to prove their semantic certificates.
- Added `scripts/compare_statement_dependencies.py`. It derives counts from classifier JSON rather than fixed output. Against the Experiment 7 baseline it reports:

| Target | Before | After | Eliminated | Percentage |
| --- | ---: | ---: | ---: | ---: |
| `big_nat_eq0` | 43 | 0 | 43 | 100.00% |
| `sum_of_ones` | 43 | 0 | 43 | 100.00% |
| `sum_le_summation_range` | 43 | 39 | 4 | 9.30% |
| **Unique union** | 43 | 39 | 4 | 9.30% |

- Machine evidence: `reports/logs/experiment8/assumption_summary_experiment9.json`, `assumptions_experiment9.log`, and `statement_dependency_comparison_experiment9.{json,md}`.

### 2026-09-19 19:41:02 HKT — full fresh end-to-end validation passed

- `REEXPORT=1 ./Validation/scripts/validate_finite_nat_sum_bridge.sh` completed with exit code 0 after compiling `Prosa/Util/Sum.lean` into two fresh, independent build directories and exporting/importing both actual artifacts.
- Fresh normalized artifact: SHA-256 `31423b3a4c8ddfb6bf3e10ae6ed0deadd1ce5eb4a770847da306eda44d86a274`; it has exactly two `#AX` declarations, the selected target signatures. Thus its transitive theorem-signature count is zero.
- Fresh fallback artifact: SHA-256 `f90e32c9ed792ed372e9e7d3173d75f779b9dbf48386a8c014f52bffe075b733`; it has 40 `#AX` declarations: one target signature plus the 39 remaining transitive signatures.
- Lean source SHA-256 recorded by both manifests: `7587b9bb16c84f61519e86bed3c5b686196454db0d9f5bc1ed0f9abbb38c468b`. Toolchain: `leanprover/lean4:v4.33.1`. Production tree remains unchanged (`git diff -- Prosa` is empty).
- Lean exporter proof of target-type provenance:
  - `big_nat_eq0`: `original_hash=3868918011`, `normalized_hash=2254104721`, `defeq=true`.
  - `sum_of_ones`: `original_hash=406666510`, `normalized_hash=2639695887`, `defeq=true`.
- Official source block and elaborated-type fidelity passed for all three targets. This checks byte-identical extracted declarations plus official-vs-generated fully explicit Rocq declaration types.
- Clean rebuild cache invalidation passed: validation-only source mutation changed artifact SHA-256 from `244b8dbe...35d6f4` to `d7fa4028...d4ea87`.
- Both mutation layers passed:
  - certificate-level `sum = 0 -> sum = 1` reuse was rejected;
  - end-to-end actual Lean `[m,n) -> [m,n]` mutation was detected using counterexample `m=n=0, F 0=1`;
  - semantics-preserving helper refactor remained accepted.
- Forbidden-proof scan found no `Admitted`, `admit`, or `sorry`. The only validation axiom remains `PropSPropFoundation.interpret_strict`.
- Generated A/B/C/D classification (`dependency_classification_experiment9.json`) is:

| Target | A: Rocq-reproved imported dependency | B: no statement axiom needed | C: avoided by representation abstraction | D: still required |
| --- | ---: | ---: | ---: | ---: |
| `big_nat_eq0` | 0 | 19 | 24 | 0 |
| `sum_of_ones` | 0 | 19 | 24 | 0 |
| `sum_le_summation_range` | 0 | 4 | 0 | 39 |

For the first two targets, B covers arithmetic/propositional proof facts removed from the semantic graph; C covers Finset/Multiset/List permutation and structure-proof dependencies bypassed by the Lean-definitionally-equal list-computation signature. For `sum_le_summation_range`, the four B entries are actual checked Lean proof bodies rather than Rocq reproofs; this distinction is deliberately recorded in the machine-generated per-dependency table.

### 2026-09-19 19:43:37 HKT — exporter patch reproducibility checked

- Regenerated `patches/lean4export-generic-statement-only.patch` as a syntactically valid unified diff against pristine lean4export commit `c9f8373f8a37a65c0ed9bfd20480a3d7481a163e`.
- A clean temporary copy accepted `git apply --check`; applying the patch produced a byte-identical `Export.lean` to the exporter used by the successful fresh run.
- The patch remains name-generic: theorem names come from mapping/configuration and no Prosa declaration is hard-coded in exporter source.

### 2026-09-19 19:47:26 HKT — artifacts organized for handoff

- Consolidated all Experiment 8/9 execution evidence under `reports/logs/experiment8/`; the validator now writes future exporter manifests and logs directly into that directory.
- Removed only disposable untracked build/inspection directories (moved to system Trash); all tracked pre-existing workspace artifacts were preserved.
- Shell syntax, Python syntax, YAML parsing, and source-file whitespace checks pass. Generated `.out` files retain lean4export's own trailing-space wire format.

## Final result

Environment and provenance:

- Frozen repository commit: `b6becfb7c6cb8317469b0be50e91c9153edf7c87`.
- Frozen production Lean tree object: `7426e874bd049e6f007b2695ef13f7209a0a1f8f`.
- Official Rocq source: Prosa 0.6, pinned source commit `414e66760333eaa4ef78c685bcf53291c527a548`.
- Lean: `leanprover/lean4:v4.33.1`; compiled `Prosa/Util/Sum.lean` SHA-256 `7587b9bb16c84f61519e86bed3c5b686196454db0d9f5bc1ed0f9abbb38c468b`.
- Rocq: `9.3+rc1`; rocq-lean-import checkout `c9f43ad5c6e8b82d96e50cb5677157bc9cf581e9`.

### Answers to the experiment questions

1. **Baseline:** 43 transitive statement-only dependencies for each target; 43 unique.
2. **Final:** 0 for `big_nat_eq0`, 0 for `sum_of_ones`, 39 for `sum_le_summation_range`; 39 unique.
3. **Eliminated:** 43, 43, and 4 respectively. The unique-union reduction is 4 because the remaining target still uses 39 members of the shared baseline set.
4. **Independently reproved imported dependencies:** none of the 43 were merely cloned under new Rocq theorem names. New Rocq computation lemmas prove only the semantic List/range/map/fold and old fallback operations required by the correspondence.
5. **Derived from smaller lemmas:** the finite-sum semantic bridge is built by induction from imported constructor equations and canonical Nat conversion; this is part of the semantic proof, not a reconstruction of Lean's original theorem-proof graph.
6. **Avoided by semantic abstraction:** for both normalized targets, 24 proof-field/Finset/Multiset/permutation dependencies were bypassed by exporting the Lean-kernel-verified definitionally equal list-computation target signature. Nineteen additional arithmetic/propositional proof dependencies became irrelevant to the semantic certificate.
7. **Still required:** the 39 fallback dependencies belong only to `sum_le_summation_range`. Plain `Meta.reduceAll` leaves its `Finset.Ico`/`Finset.sum` under an implication/existential proposition, while full delta expansion exposes quotient, permutation, locally-finite-order, and structure proof fields. A smaller audited signature for this target therefore remains `BLOCKED_BY_IMPORTED_REPRESENTATION`; it is not a demonstrated translation mismatch.
8. **Status change:** `big_nat_eq0` and `sum_of_ones` improve from `CERTIFIED_WITH_PROP_SPROP_FOUNDATION_AND_STATEMENT_EXPORT` to `CERTIFIED_WITH_PROP_SPROP_FOUNDATION`. `sum_le_summation_range` retains the former status but has 4 fewer statement assumptions.

The exact target theorem signature remains a provenance boundary, not a semantic assumption: each selected compiled theorem type is exported under its actual declaration name, and the normalized signatures are accepted only after Lean kernel definitional-equality checking. The target theorem itself is absent from each certificate's `Print Assumptions` result.

## Trust boundary

- Lean kernel checks the original theorem proof against its compiled type.
- lean4export emits the selected theorem signature; for two targets it also records a kernel-checked `isDefEq` normalization result and hashes of both expressions.
- rocq-lean-import and its declared primitives/definitional-UIP representation form the importer boundary.
- `PropSPropFoundation.interpret_strict` is the sole validation axiom.
- There are no validation-specific semantic premises, unexpected axioms, target-theorem self-dependencies, `Admitted`, `admit`, or `sorry`.
- The remaining 39 signatures for `sum_le_summation_range` are explicitly visible and classified; they are not hidden or promoted to foundation assumptions.

## Reproduction

From `Prosa-fei/`:

```bash
REEXPORT=1 ./Validation/scripts/validate_finite_nat_sum_bridge.sh
```

This command performs official-source extraction, two fresh Lean builds, actual-artifact export/import, Rocq certificate compilation, per-certificate `Print Assumptions` classification, source elaborated-type fidelity checking, cache invalidation testing, certificate mutation rejection, end-to-end interval mutation, and automatic before/after statistics.

## Main implementation artifacts

- `patches/lean4export-generic-statement-only.patch`: generic statement-only and definitionally-normalized type export.
- `rocq/ImportedFiniteNatSumNormalized93.v`: imports the minimal two-signature actual artifact.
- `rocq/HardSumCertificate.v`, `FiniteNatSumBridge.v`, `FiniteNatSumReuseCertificates.v`: independent semantic proofs over imported computation.
- `rocq/AssumptionAuditFiniteSumExperiment9.v`: the three authoritative assumption queries.
- `mapping/hard_validation_targets.yaml`, `experiment9_assumption_audit.yaml`: export/status/audit configuration.
- `scripts/compare_statement_dependencies.py`, `classify_statement_dependency_reduction.py`: machine-derived counts and A/B/C/D classification.
- `reports/logs/experiment8/full_fresh_validation_run.log`: successful complete run.

## Next minimal step

For `sum_le_summation_range`, implement a generic target-type projection that normalizes the finite-sum subexpression while preserving the implication/existential shell, with Lean `isDefEq` as the mandatory acceptance check. If Lean cannot establish definitional equality, retain the 39 dependencies rather than introducing an axiom or a hand-written approximate target type.
