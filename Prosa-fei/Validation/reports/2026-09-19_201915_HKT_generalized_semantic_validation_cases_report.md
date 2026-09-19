# Generalized Semantic Validation Cases Report

**Experiment:** 10, following Experiment 9  
**Start:** 2026-09-19 20:19:15 HKT  
**Frozen repository commit:** `f52cdc932724a0f63320f63ea732d3fbdc5405ca`  
**Frozen production-tree object:** `7426e874bd049e6f007b2695ef13f7209a0a1f8f`  
**Official source:** Prosa 0.6, pinned commit `414e66760333eaa4ef78c685bcf53291c527a548`  
**Constraint:** no modification under `Prosa-fei/Prosa/`.

## Progress log

### 2026-09-19 20:19:15 HKT — baseline and source mismatch confirmed

- Experiment 9 baseline loaded: `sum_le_summation_range` has 39 remaining transitive statement-only dependencies; `big_nat_eq0` and `sum_of_ones` have zero.
- Selected `JobArrival` as the full small-class correspondence case. Both source and target are single-field classes whose complete observable content is `Job -> instant`; the existing result currently proves only preservation of that projection under a canonical source-to-target map.
- Official Prosa 0.6 `behavior/service.v` defines `completes_at` as `(~~ completed_by j t.-1 || (t == 0)) && completed_by j t`.
- Frozen production Lean defines it as `¬ completed_by sched j (t - 1) ∧ completed_by sched j t`, omitting the `t = 0` disjunct. Since Nat subtraction saturates, at `t = 0` the Lean formula reduces to `¬ completed_by 0 ∧ completed_by 0`, whereas the source formula reduces to `completed_by 0`. This is a concrete mismatch candidate; it will be marked `FAILED_SEMANTIC_EQUIVALENCE` only after a Rocq-kernel-checked counterexample over actual imported Lean computation is completed.

## Current machine-checked status

No new target status is claimed yet. The observations above are source inspection and reduction analysis pending the new certificates.

### 2026-09-19 20:31:58 HKT — complex-shell normalization closed the 39-dependency gap

- Implemented a generic recursive target-type subexpression projection mechanism in the lean4export patch. Its configured `Finset.sum` rule recognizes a fully applied Nat `Finset.sum (Finset.Ico lower upper) f` and constructs the corresponding `List.range'` / `List.map` / `List.foldr` computation.
- The transformation is fail-closed: the exporter runs `Lean.Meta.isDefEq` between the actual compiled theorem type and the complete projected type, and aborts if Lean does not establish definitional equality.
- For actual compiled `Prosa.Util.Sum.sum_le_summation_range`, Lean logged `original_hash=1525648494`, `normalized_hash=229062228`, `original_constants=18`, `normalized_constants=17`, `defeq=true`.
- The projected artifact containing all three finite-sum theorem signatures has SHA-256 `6248e5885af1212b0a3019e0e4b7f04aae60554a23c5ff97d4457a92ae5e9d2e`, 1,404 lines, and exactly three `#AX` entries—the three target signatures. It contains zero transitive theorem signatures.
- Reconnected `sum_le_summation_range_statement_certificate` to the projected actual artifact. Rocq 9.3 accepted the existing independent semantic proof over `List.range'`, `List.map`, and `List.foldr`.
- Automatic `Print Assumptions` classification now reports `CERTIFIED_WITH_PROP_SPROP_FOUNDATION`, with `statement_only_dependencies=[]`, `semantic_premises=[]`, `target_theorem_dependency=false`, and `unexpected=[]`.
- Result: `sum_le_summation_range` transitive statement dependencies are reduced **39 -> 0**. The complex implication/existential/conjunction/order shell is preserved; only the computational finite-sum subexpression is projected.

### 2026-09-19 20:33:53 HKT — `JobArrival` upgraded to full bidirectional class correspondence

- Added `rocq/JobArrivalClassCertificate.v`, directly using the actual imported Lean `Prosa_Behavior_Job_JobArrival` constructor and projection from `RTSValidation.out`.
- Defined both maps: `import_job_arrival` (official Rocq class -> imported Lean class) and `export_job_arrival` (imported Lean class -> official Rocq class).
- Defined a complete field relation and observational equalities on both sides. This is the correct representation-aware notion: official Rocq 0.6 elaborates the single-field class definitionally to `Job -> instant`, while Lean represents it as a one-field structure. Literal function/record equality would unnecessarily require functional extensionality.
- Rocq 9.3 kernel accepted constructor correspondence, arbitrary target-to-source correspondence, projection completeness, source roundtrip, and target roundtrip.
- `Print Assumptions` shows only importer `eq` definitional UIP where imported equality is used; source roundtrip is closed under the global context. There is no semantic premise and no Prop/SProp interpretation axiom.
- Since `job_arrival` is the only field, field-observational equality covers the complete class representation. The former projection-only result is upgraded to **FULL_CLASS_CORRESPONDENCE / CERTIFIED**.

### 2026-09-19 20:44:05 HKT — completes-at actual-artifact fixture exported; Rocq import in progress

- Added `lean_fixtures/completes_at_corrected/CompletesAtCorrected.lean`. It defines a concrete zero-cost `Unit` job/processor fixture, a wrapper that calls the frozen production `Prosa.Behavior.Service.completes_at`, the generic corrected formula with the official source's `t = 0` branch, and a corrected concrete wrapper.
- The fixture compiled with Lean `v4.33.1` without `sorry`. Its source SHA-256 is `10f3946ed6f331cfeace69af5d54c49a19096a29cc61f6aa220b5c15ab797cf1`.
- A fresh rebuild exported all four relevant actual constants, including the production `completes_at`, into `RTSValidation.out`. Artifact SHA-256 is `d18a451f91f651cc0d524d04499c08e9fc4cd4a81a28af9b6a7e1f34ae9d59c9`.
- Rocq 9.3 import is currently running. No mismatch/pass status is claimed at this checkpoint: the next required evidence is a kernel-checked proof that the imported production wrapper is false at zero and the imported corrected wrapper is true under the same concrete specification.

### 2026-09-19 21:08:17 HKT — production mismatch rejected and corrected fixture certified

- The first full 4.35 MB import was terminated after 22 minutes because it traversed irrelevant service/Mathlib implementation dependencies. This run produced no certificate and is retained only as a scalability diagnostic in `logs/experiment10/import_rts_with_completes_at.log`.
- Implemented a generic validation-artifact definition-body projection. Its configuration supplies `source=replacement=rfl_guard`; the exporter verifies that the guard is an actual compiled Lean theorem whose exact type equates the named source and replacement constants and whose proof body is `Eq.refl`. It then exports the source constant under its original name with the smaller definitionally identical body. A malformed/non-`rfl` guard aborts export.
- For both zero-time wrappers Lean compiled `@[defeq] ... := rfl` guards against explicit normal forms. The resulting actual-artifact export is 3,004 bytes / 196 lines, SHA-256 `d1a7c2a57c9d8c4959d55e85118b2ff60eeb138751141cfcf5f92335d9111deb`. Rocq 9.3 imported it successfully in under one second.
- Added `rocq/CompletesAtSemanticCertificate.v`. The official-source witness fixes job cost to zero and time to zero; MathComp evaluation proves official `completes_at` true for every processor state/schedule/job because `[0,0)` service is zero and the source definition contains `(t == 0)`.
- Rocq proves the actual imported frozen-production proposition uninhabited: it is definitionally `And (Not (0 <= 0)) (0 <= 0)`. The certificate packages the source inhabitant and target negation together in `completes_at_current_counterexample_witness : SProp`.
- Rocq proves the imported corrected fixture inhabited and establishes `PropSPropRel` to the same official source statement in `completes_at_corrected_certificate`.
- `Print Assumptions` reports the source proof, target rejection, and counterexample closed under the global context. The corrected inhabitant/certificate expose only the importer's documented definitional-UIP assumption for imported equality; `PropSPropFoundation.interpret_strict` is not needed.
- Formal statuses: frozen production **FAILED_SEMANTIC_EQUIVALENCE** with kernel-checked witness `t = 0`, `job_cost = 0`; validation-only corrected fixture **CERTIFIED** (modulo the standard importer equality foundation already tracked globally).

### 2026-09-19 21:12:03 HKT — source fidelity and automatic assumption audit closed

- Automatic source extraction read `behavior/service.v` from pinned commit `414e66760333eaa4ef78c685bcf53291c527a548`. Exact `completes_at` block SHA-256 is `80487d6bc2e7e4de763c5d67c7a42f67fe524a910db3719043d596710929e76a`; normalized statement SHA-256 is `c7db1c554357a9c853005118d24b53b1f287379a473df183539fffdb521b0c8c`.
- `CompletesAtSourceFidelity.v` directly imports the official module. Rocq prints the elaborated declaration as `(~~ completed_by ... t.-1 || (t == 0)) && completed_by ... t`, with type `schedule PState -> JobCost Job -> Job -> instant -> bool`.
- Added mapping entries for current and corrected `completes_at`, including official source provenance, actual Lean source, projection guard, certificates, assumptions, and distinct statuses.
- Automatic per-certificate assumption classification now reports:
  - `job_arrival_full_class`: `CERTIFIED`, only importer definitional UIP;
  - `completes_at_current_counterexample`: the counterexample evidence itself is `CERTIFIED`, with no assumptions;
  - `completes_at_corrected`: `CERTIFIED`, only importer definitional UIP.
- The status of the target translation remains **FAILED_SEMANTIC_EQUIVALENCE**: a closed proof of a counterexample is evidence of failure, not a successful correspondence certificate.

### 2026-09-19 21:19:14 HKT — default fresh run and final Experiment 10 matrix

The new driver `scripts/validate_generalized_semantic_cases.sh` passed its default fresh-export path. It rebuilt all selected Lean sources into fresh directories, re-exported all three artifacts, compiled the Rocq certificates, classified `Print Assumptions`, reran cache invalidation, and reran the end-to-end interval-endpoint mutation.

| Target | Actual compiled Lean involved? | Correspondence evidence | Assumption audit | Status |
| --- | --- | --- | --- | --- |
| `sum_le_summation_range` | yes; exact target type, local `Finset.sum` projection accepted by `Meta.isDefEq` | bidirectional statement relation; complex implication/existential/conjunction/order shell preserved | only `PropSPropFoundation.interpret_strict` plus importer primitives; no semantic premise, target self-dependency, transitive statement dependency, or unexpected axiom | `CERTIFIED_WITH_PROP_SPROP_FOUNDATION` |
| `JobArrival` | yes; actual imported constructor and projection from `RTSValidation.out` | source→target map, target→source map, constructor/projection preservation, and two observational roundtrips | importer definitional UIP only | `CERTIFIED` / `FULL_CLASS_CORRESPONDENCE` |
| production `completes_at` | yes; fresh compiled wrapper calls the frozen production definition and its smaller exported body is guarded by an exact compiled `Eq.refl` theorem | source inhabitant plus imported-target negation in one Rocq-kernel-inhabited `SProp` counterexample package | closed under global context | `FAILED_SEMANTIC_EQUIVALENCE` |
| corrected `completes_at` fixture | yes; fresh compiled validation-only definition and `Eq.refl`-guarded body projection | `PropSPropRel` against the same official source statement and the same zero-time/cost specification | importer definitional UIP only; no `interpret_strict` | `CERTIFIED` |

## Answers to the research questions

1. **Final dependency count:** `sum_le_summation_range` moved from the Experiment 9 machine-generated count of 39 transitive statement exports to **0**. All 39 disappeared because the semantic artifact no longer follows the Lean proof dependency graph; none were individually re-proved.
2. **Complex logical-shell normalization:** successful. The exporter recursively finds the Nat `Finset.sum (Finset.Ico ...)` subexpression, projects only that computation, preserves implication/existential/conjunction/order, and requires `Lean.Meta.isDefEq Q Q'` before emitting the target type.
3. **Simple class:** `JobArrival`, selected because it has exactly one semantically complete field, `Job -> instant`.
4. **Full two-sided class result:** yes, modulo explicit field-observational equality (the axiom-free representation-aware alternative to function extensionality). Both maps and both roundtrips are checked; there is no semantic premise.
5. **Projection-only upgraded:** yes, to `FULL_CLASS_CORRESPONDENCE`.
6. **Production `completes_at` mismatch:** yes, formally established rather than inferred from a failed proof attempt.
7. **Counterexample:** `t = 0`, `job_cost j = 0`. Official Prosa evaluates to `completed_by j 0`, hence true because service and cost are both zero. Frozen Lean evaluates to `¬ completed_by j 0 ∧ completed_by j 0`, hence false.
8. **Corrected validation-only fixture:** the formula `(¬ completed_by (t - 1) ∨ t = 0) ∧ completed_by t` passes the same zero-time semantic specification and is `CERTIFIED`. Production Lean was not modified.

## Hardening results

- Fresh build manifests record Lean `v4.33.1`, repository commit `f52cdc932724a0f63320f63ea732d3fbdc5405ca`, production tree `7426e874bd049e6f007b2695ef13f7209a0a1f8f`, build directories, source hashes, and artifact hashes.
- Official Rocq source is pinned to `414e66760333eaa4ef78c685bcf53291c527a548`; the extracted `completes_at` block and directly elaborated official type agree.
- Automatic assumption classification reports no semantic premises, no unexpected assumptions, and no target-theorem self dependency.
- Cache invalidation: `PASS` (`244b8dbe...` changed to `d7fa4028...` after a validation-only source mutation).
- End-to-end interval mutation `[m,n)` → closed endpoint: `PASS`, with concrete witness `m=n=0`, `F 0=1`. Semantics-preserving helper refactor control also passes.
- Forbidden-proof scan covers the new Rocq certificates and Lean fixture. No `Admitted`, `admit`, or `sorry` occurs. The only allowed validation axiom remains `PropSPropFoundation.interpret_strict`; the new class/completes-at results do not use it.
- `git diff -- Prosa` is empty: the frozen production translation was not changed.

## Reproduction

```bash
cd Prosa-fei
./Validation/scripts/validate_generalized_semantic_cases.sh
```

The default performs fresh Lean rebuild/export. Set `REIMPORT_RTS=1` to force re-import of the unchanged 2.68 MB canonical RTS artifact; otherwise the driver requires its exact known SHA-256 and an existing kernel-checked `ImportedEasy93.vo`. The smaller finite-sum and completes-at artifacts are always re-imported.

Artifact SHA-256 values from the final fresh run:

- `FiniteNatSumNormalizedTargets.out`: `6248e5885af1212b0a3019e0e4b7f04aae60554a23c5ff97d4457a92ae5e9d2e`
- `CompletesAtValidation.out`: `d1a7c2a57c9d8c4959d55e85118b2ff60eeb138751141cfcf5f92335d9111deb`
- `RTSValidation.out`: `60f07832ce3bdc4c8d940ead5afbfef94ed4600fabf65113bb4ebd31ee9d590b`
- exporter patch: `38ece7882097f4a34496ec738b3402e87e2c92a7f7dc54a6a92925c6e2e4d9ab`

## Trust-boundary note

The sum theorem needs the isolated `SProp -> Prop` interpretation principle. `JobArrival` does not. The current `completes_at` counterexample is closed, and the corrected relation needs only rocq-lean-import's documented definitional-UIP treatment for imported equality. The validation-only body projection does not assert a semantic axiom: export is permitted only after Lean has compiled an exact equality guard whose proof term is syntactically `Eq.refl`; malformed guards fail closed.

### 2026-09-19 21:21:45 HKT — final integrity check

- Shell syntax, YAML parsing, patch dry-run, and `git diff --check` all pass.
- The finite-sum artifact contains exactly three `#AX` entries, one per target theorem signature.
- Export logs retain `defeq=true` for the `sum_le_summation_range` projected type and `kernel_rfl_guard=true` for both completes-at normal forms.
- Production-tree diff remains empty.
