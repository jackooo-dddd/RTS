# Generalization, Kernel Guards, and False-Positive Resistance Report

**Experiment:** 11, following Experiment 10  
**Start:** 2026-09-19 22:31:21 HKT  
**Frozen repository commit:** `f52cdc932724a0f63320f63ea732d3fbdc5405ca`  
**Production constraint:** no changes under `Prosa-fei/Prosa/`.

## Progress log

### 2026-09-19 22:31:21 HKT — baseline fixed

- Experiment 10 machine-checked baseline loaded: `sum_le_summation_range` has zero transitive statement dependencies; `JobArrival` has full observational class correspondence; production `completes_at` has a closed zero-time counterexample; the corrected fixture is certified only for `t=0`, zero cost.
- This experiment will not call the concrete corrected result generic. The first target is a compositional theorem parameterized by an explicit `completed_by` semantic relation; unless that relation is closed for a concrete processor model, the status will remain `CONDITIONAL`.
- The existing exporter evidence is `Meta.isDefEq`; this experiment separately adds declarations admitted to the Lean environment with an `Eq.refl` proof term and records these as kernel guards. The two evidence layers will be reported separately.

### 2026-09-19 22:36:35 HKT — kernel-checkable finite-sum normalization guards pass

- Added `Validation/lean_tools/FiniteSumNormalizationGuards.lean`. It reads each theorem's type from the current compiled Lean environment, applies the same `Finset.sum (Finset.Ico ...)` projection as the exporter, first checks `Meta.isDefEq`, then adds a theorem whose type is `originalType = normalizedType` and whose proof term is `Eq.refl originalType`. The resulting `.olean` was accepted by Lean 4.33.1.
- All three guards passed. Their original/normalized expression hashes exactly match the exporter audit:
  - `big_nat_eq0`: `3868918011 -> 783880789`
  - `sum_of_ones`: `406666510 -> 1612875744`
  - `sum_le_summation_range`: `1525648494 -> 229062228`
- This is stronger evidence than the exporter-side `Meta.isDefEq` check alone: the actual equality declaration has an `Eq.refl` proof checked while producing the guard `.olean`. It remains a validation-only guard and does not change production Lean.
- Added `FiniteSumNormalizationBadIdentity.lean`. It changes the projected fold identity from `0` to `1`. Compilation exited `1` with `EXPECTED_REJECTION: bad fold identity is not definitionally equal`; consequently no kernel guard can be constructed.
- Commands and full output: `reports/logs/experiment11/normalization_guards.log` and `normalization_bad_identity.log`.

### 2026-09-19 22:42:46 HKT — corrected `completes_at` generalized compositionally

- Extended only the validation fixture, not production, with `completes_at_formula : (Nat -> Prop) -> Nat -> Prop` and a compiled `rfl` theorem tying the actual corrected fixture to that formula: `completes_at_corrected_formula_defeq`.
- Freshly compiled and exported the actual formula definition. `CompletesAtValidation.out` now has SHA-256 `a13065be3f2c12f5783a1ec4557b815b208b5fc4ce1a25f2bd63827cb6485f51`; `rocq-lean-import` successfully imported it as `Prosa_Validation_CompletesAt_completes_at_formula`.
- Added `rocq/CompletesAtGenericCertificate.v`. Its theorem `official_completes_at_conditional_certificate` directly mentions the official pinned Prosa declaration `prosa.behavior.service.completes_at`, works for arbitrary Rocq job type, processor state, schedule, job, cost instance, and time, and relates it to the actual imported corrected formula.
- The proof is structural over zero/successor time and both truth values of the prior completion predicate. It does not prove both sides independently. Its sole semantic premise is pointwise `SourceCompletedByRel`, i.e. semantic correspondence of official `completed_by` and the Lean-side completion predicate.
- Rocq 9.3 accepted the certificate. `Print Assumptions` reports only importer definitional UIP and `PropSPropFoundation.interpret_strict`; the `Hcompleted` relation is an ordinary explicit theorem parameter and is therefore tracked as an open semantic premise by policy.
- Status: **CONDITIONAL** (generic over all processor models, schedules, jobs, costs and times; not closed for Ideal because `completed_by/service` correspondence remains outside the certified slice).
- Logs: `reports/logs/experiment11/completes_at_export_manifest.log`, `imported_completes_at.log`, and `completes_at_generic_certificate.log`.

### 2026-09-19 22:44:40 HKT — false-positive and fail-closed audit tests pass

- Strengthened `classify_assumptions.py` with paired `AUDIT_BEGIN`/`AUDIT_END` sections, explicit exact-name allowlists, and an option that disables legacy prefix trust. In strict mode an unfinished section is not treated as a clean empty assumption set.
- Compiled `FalsePositiveAuditFixtures.v` and classified its real `Print`/`Print Assumptions` output:
  - semantic correspondence supplied as theorem hypothesis: `CONDITIONAL`;
  - `fake_semantic_axiom`: `FAILED_ASSUMPTION_AUDIT` and unexpected assumption named explicitly;
  - certificate using `Prosa_Util_Sum_big_nat_eq0` itself: `FAILED_ASSUMPTION_AUDIT`, `target_theorem_dependency=true`.
- The strict fixture has `allow_legacy_prefixes: false`; the fake axiom is rejected by identity/content, not merely because its name lacks an approved prefix.
- Added and ran `test_assumption_audit_fail_closed.sh`: both a missing log and a log truncated after `AUDIT_BEGIN` are classified `AUDIT_MISSING`, and the classifier exits nonzero.
- Added content-addressed `artifact_provenance.py` and `test_stale_artifact_rejection.sh`. A changed validation-only Lean source with the old export/import, and a changed export with the old imported `.vo`, were both rejected as stale.
- Logs and structured evidence: `false_positive_assumptions.log`, `false_positive_summary.json`, `false_positive_classification.log`, `fail_closed_assumption_test.log`, and `stale_artifact_test.log`.

### 2026-09-19 22:53:41 HKT — independent clean reproduction succeeds

- Added and ran `scripts/clean_reproduce_experiment11.sh`. It created `/var/folders/_8/9c_9khxs23l6fy43zqp93gmh0000gn/T/prosa-exp11-clean.sy8qp8/TranslationProof`, copied source while excluding all `.olean`, `.vo`, `.glob`, `.aux`, prior export `.out` files, prior logs, and `Validation/.work`, and reused only the fixed external Lean/Mathlib/Rocq/importer toolchains.
- The first clean attempt correctly failed because `FiniteNatSumReuseCertificates.v` had a hidden dependency on `ImportedBigNatEq093.vo` that the normal worktree supplied. The script was fixed to freshly export and import that definition graph too. The second run started from another new directory and completed. This is evidence that clean reproduction is detecting hidden local-object reuse rather than silently tolerating it.
- Official source extraction was repeated from Prosa v0.6 commit `414e66760333eaa4ef78c685bcf53291c527a548`. The elaborated official `completes_at` type/body was printed again; the source block hash remains `80487d6bc2e7e4de763c5d67c7a42f67fe524a910db3719043d596710929e76a`.
- Clean artifact SHA-256 values:
  - normalized finite sums: `6248e5885af1212b0a3019e0e4b7f04aae60554a23c5ff97d4457a92ae5e9d2e`;
  - finite-sum definition graph: `20aefd4c4cd26b73c196b6c7e74a109efa565cd3214d1938f92bd4415daa1f69`;
  - minimal JobArrival: `7a00869600f9725c8ac8b79a8489dc2e5055211d7e51e58d8655d00c62f2056d`;
  - completes-at validation: `a13065be3f2c12f5783a1ec4557b815b208b5fc4ce1a25f2bd63827cb6485f51`.
- `artifact_provenance.py` then verified the exact source/export/imported-object tuple. Imported `.vo` hashes and all source hashes are in `logs/experiment11/clean_reproduction/clean_artifact_provenance.json`.
- Clean statuses from the strict automatic assumption audit:

| Target | Clean status | Semantic premise | Unexpected assumptions | Target self-dependency |
|---|---|---:|---:|---:|
| `big_nat_eq0` | `CERTIFIED_WITH_PROP_SPROP_FOUNDATION` | none | none | false |
| `sum_le_summation_range` | `CERTIFIED_WITH_PROP_SPROP_FOUNDATION` | none | none | false |
| `JobArrival` two-sided field roundtrip | `CERTIFIED` | none | none | false |
| production `completes_at` counterexample | evidence `CERTIFIED`; production translation remains `FAILED_SEMANTIC_EQUIVALENCE` | none | none | false |
| corrected concrete `completes_at` | `CERTIFIED` | none | none | false |
| corrected generic `completes_at` composition | `CONDITIONAL` | `Hcompleted : SourceCompletedByRel ...` | none | false |

- The three finite-sum kernel guards were rebuilt in the clean tree and repeated the same expression hashes. The wrong-identity negative guard again failed before a declaration could be added.
- Full copied evidence is under `reports/logs/experiment11/clean_reproduction/`; the one-line outcome is `clean_reproduction_summary.log`.

## Final answers

1. **How far was corrected `completes_at` generalized?** To arbitrary official Rocq job type, processor state, schedule, job-cost instance, job and time, against an actual imported validation-only Lean formula definition that is tied by a compiled `rfl` theorem to the corrected fixture. It is not yet a closed Ideal/service theorem.
2. **Does a semantic premise remain?** Yes. The generic theorem requires exactly pointwise `completed_by` correspondence (`SourceCompletedByRel`). It is therefore `CONDITIONAL`, not certified. The earlier zero-cost/time-zero corrected case remains closed and `CERTIFIED`.
3. **Is normalization kernel-guarded?** Yes. Export still performs `Meta.isDefEq`. Separately, Lean compiles an equality declaration for each actual original/normalized type with proof `Eq.refl`; those are the kernel-checkable guards. The report does not equate the Meta check alone with a kernel proof.
4. **Was wrong normalization rejected?** Yes. Changing fold identity from `0` to `1` makes `Meta.isDefEq` false, compilation exits nonzero, and no `Eq.refl` guard is admitted.
5. **Are false premises, fake axioms and circular dependencies detected?** Yes. A semantic premise becomes `CONDITIONAL`; a fake axiom fails the audit; a direct target-theorem dependency fails with `target_theorem_dependency=true`.
6. **Are stale artifacts detected?** Yes. Content-addressed provenance rejects both source-change/old-artifact and artifact-change/old-import combinations. Export scripts themselves build into fresh directories.
7. **Did clean reproduction succeed?** Yes, on the second from-scratch run after the first run exposed and caused removal of a hidden `.vo` reuse. All five requested representative categories were rebuilt, imported, kernel checked and automatically classified.
8. **Remaining trust boundary:** Lean 4.33.1 checks the frozen production artifact and validation-only `rfl` guards; `lean4export` plus `rocq-lean-import` transports declarations; Rocq 9.3+rc1 checks certificates; imported equality carries the importer's documented definitional-UIP treatment; theorem-level Prop/SProp results use the single isolated `PropSPropFoundation.interpret_strict` axiom. The generic corrected `completes_at` result additionally has the explicitly visible, non-trusted-but-unclosed `completed_by` semantic premise. Exact target type provenance remains a necessary export boundary. No production Lean file changed, and no successful certificate uses `Admitted`, `admit`, `sorry`, or a new semantic axiom.

## Reproduction commands

```bash
cd Prosa-fei
./Validation/scripts/clean_reproduce_experiment11.sh
./Validation/scripts/test_assumption_audit_fail_closed.sh
./Validation/scripts/test_stale_artifact_rejection.sh
```

Toolchains used: Lean `4.33.1`; Rocq `9.3+rc1`; official Prosa source commit `414e66760333eaa4ef78c685bcf53291c527a548`; frozen production tree `7426e874bd049e6f007b2695ef13f7209a0a1f8f`.
