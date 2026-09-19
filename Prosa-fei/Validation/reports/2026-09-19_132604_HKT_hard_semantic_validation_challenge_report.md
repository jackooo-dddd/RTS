# Hard Semantic Validation Challenge Report

**Experiment 5 start:** 2026-09-19 13:26:04 HKT  
**Repository commit at start:** `e58fad33bfe0b827ea39b23fc324027d574899c6`  
**Scope:** frozen modern Prosa translation; no files under `Prosa-fei/Prosa/` may be modified.

## Progress log

### 2026-09-19 13:26:04 HKT — target inventory started

- Confirmed Lean targets in `Prosa/Util/Sum.lean`: `sum_seq_gt0P`, `big_nat_eq0`, `sum_diff`, and stretch target `sum_pred_diff`.
- Confirmed Lean recursive definition and theorem in `Prosa/Util/List.lean`: `rem_all` and `nin_rem_all`.
- Confirmed Lean complex proposition theorem in `Prosa/Util/Step_function.lean`: `StepFunction.exists_first_intermediate_point`.
- Confirmed Lean custom inductive and matcher in `Prosa/Model/Processor/Spin.lean`: `processor_state` with `Idle`, `Spin`, `Progress`, plus `spin_scheduled_on`.
- Located official Prosa 0.6 `big_nat_eq0` in `util/sum.v`, `rem_all`/`nin_rem_all` in `util/list.v`, and the Spin declarations in `model/processor/spin.v`.
- The initially suggested official path `util/step_function.v` does not exist in this release; exact source provenance is being resolved before configuration.
- At this timestamp no new certificate has been claimed and no production translation has been changed.

### 2026-09-19 13:28:53 HKT — source provenance and direct-import feasibility established

- Exhaustive search of the pinned official Prosa 0.6 source tree confirmed that `sum_seq_gt0P`, `sum_diff`, and `sum_pred_diff` do not exist anywhere in that release. They exist only in the frozen Lean snapshot. Unless an exact alternative Rocq provenance is found, these are genuine 1:1 source-target validation failures, not missing validator bridges.
- Resolved `exists_first_intermediate_point` to official `util/unit_growth.v`; this exposes a stale Lean source comment (`util/step_function.v`) but not yet a statement mismatch.
- Rocq 9.3 directly compiled official `util/list.v` and `model/processor/spin.v` without statement or proof changes.
- Direct compilation of complete `util/sum.v` fails before `big_nat_eq0` at line 172 due to MathComp-2.6 rewrite drift around `big_filter_cond`. Direct compilation of complete `util/unit_growth.v` reaches line 286 but fails after the target theorem with `Cannot find witness`. Therefore target-scoped automatic extraction remains necessary for these two files; these are unrelated legacy-proof compatibility failures.
- Official whole-file SHA-256 values: `util/sum.v` = `3415b2c1d3d7ed892a168d114f66007913a014a1ec3ede2ba8fef84217bb14d5`; `util/list.v` = `cbe98e2414d4e7829b7a5f73995f9e47d5160be154406d12614283b54b3dbff3`; `util/unit_growth.v` = `c74cc6169150abdf2401953588c36f5744bf780def785ab084f8c3299e8d178b`; `model/processor/spin.v` = `cd7d2249a3600cb66c3710f967d54ebb9f13ce5690b1ffc2a99fe2d2ecf8f4de`.

### 2026-09-19 13:57:14 HKT — multi-file extraction and first hard artifact operational

- Extended the configuration-driven extractor to recognize theorem, `Definition`/`Fixpoint`, and `Inductive` blocks across multiple source files. It now emits one exact `.vfrag` snapshot per official file and one combined fidelity manifest.
- Added automatic target-scoped Rocq module generation. It discovers same-file declaration dependencies and reconstructs active Section binders from official source; declaration blocks remain byte-identical. This avoided unrelated Rocq-9.3 failures in the complete legacy files.
- Rocq 9.3 kernel compiled generated modules for `util/list.v`, `util/sum.v`, and `util/unit_growth.v`. `Print Assumptions` reports `big_nat_eq0`, `nin_rem_all`, and `exists_first_intermediate_point` closed under the global context.
- Exported all selected actual Lean declarations from the frozen snapshot. Unified artifact `HardValidation.out`: 180,886 lines, 4,160,781 bytes, SHA-256 `85e5b782bbdca4229840d532c04cdca4219350af75aaa8da42f190bcc9198914`.
- The unified artifact triggers a very expensive importer path through Mathlib's finite-sum and arithmetic dependencies and is still being processed; no unified-import success is claimed yet.
- To obtain progress independently of that cost, exported the recursive-list/custom-inductive slice as `HardCoreValidation.out`: 873 lines, 14,965 bytes, SHA-256 `b546b2257e12872d159afcdc1f4c6e64ae7678d7b5e4ea93bd73ad2400142b96`. Rocq 9.3 imported it successfully, exposing actual compiled `rem_all`, `nin_rem_all`, Spin state constructors, and `spin_scheduled_on`.
- No selected Lean file contains `sorry`; Lean proof completion and cross-ITP statement validation therefore need not be split for these targets.

### 2026-09-19 14:01:55 HKT — custom inductive and matcher certified

- Defined a constructor-level `SpinStateRel` between official Prosa 0.6 `processor_state` and the actual imported Lean inductive.
- Rocq kernel accepted individual certificates for `Idle`, `Spin j`, and `Progress j`; each is closed under the global context.
- Added a reusable `eqType` → imported `DecidableEq` implementation derived from MathComp reflection, plus Boolean equality preservation.
- Rocq kernel accepted `spin_scheduled_on_certificate` by exhaustive constructor correspondence. `Print Assumptions` contains only importer definitional UIP entries (`eq`, `Hard_STrue`), with no validation axiom and no Prop/SProp trust bridge.
- Status: `processor_state` **CERTIFIED**; `spin_scheduled_on` **CERTIFIED**.

### 2026-09-19 14:43:33 HKT — actual recursive `rem_all` body certified

- Rocq 9.3 accepted `rem_all_recursive_certificate`, relating the automatically extracted official Prosa 0.6 `Fixpoint rem_all` to `Prosa_Util_List_rem_all` from the actual compiled Lean artifact.
- The Lean implementation is represented after import by `List.brecOn`/`List_brecOn_go`, rather than a syntactically similar structural fixpoint. The certificate unfolds that course-of-values recursor and proves the relation by structural induction over the source `seq`.
- Added reusable imported equality composition and imported `ite` branch lemmas. The latter avoid relying on fragile reduction of explicit Lean `Decidable` proof arguments.
- `Print Assumptions rem_all_recursive_certificate` reports only `eq relies on definitional UIP`; there is no validation axiom and no Prop/SProp trust bridge. Status: **CERTIFIED**.
- Attempted `nin_rem_all` composition next. Its recursive-definition dependency is now closed, but the theorem remains **BLOCKED_BY_VALIDATOR_LIMITATION** at the dependent elimination needed to translate actual imported `List.Mem` (an `SProp`) back to MathComp Boolean membership. The incomplete theorem bridge is commented as work in progress and is not compiled or claimed.
- Machine-check command: `opam exec --switch=rocq93rc1 -- rocq c -R ~/.opam/prosa-0.6/.opam-switch/sources/rocq-prosa.0.6 prosa -Q /private/tmp/rocq-lean-import-93/src LeanImport -I /private/tmp/rocq-lean-import-93/src -Q generated_hard HardSource HardCoreCertificates.v` (run from `Validation/rocq`; exit 0).

### 2026-09-19 14:53:08 HKT — complex higher-order proposition certified with explicit sort bridge

- Exported only `Prosa.Util.Step_function.StepFunction.exists_first_intermediate_point` from the frozen compiled Lean module. The target-scoped artifact has 236 lines / 3,552 bytes, SHA-256 `c3fb77511b70d968523d5e4ae51f3a1b7df26edf47f998a7a11fcfc32ccfe78c`, and imports successfully with Rocq 9.3.
- Confirmed the exact imported type contains the expected higher-order `P : Nat -> Bool`, three premises, witness-carrying `Exists`, nested `And`, universal quantification, negation, and Nat `LE`/`LT`.
- Added reusable Nat conversion/roundtrip, Nat-order, Bool truth/negation, conjunction, and higher-order predicate relations in `HardStepFunctionCertificate.v`.
- Rocq kernel accepted the bidirectional `exists_first_intermediate_point_statement_certificate`. It relates predicates pointwise at related Nat arguments and derives every logical constituent compositionally; neither the official theorem proof nor the imported Lean theorem axiom is used by the correspondence proof. Separate type witnesses tie both exact declaration names to the propositions being related.
- The experiment exposed a sharper Prop/SProp boundary: transferring a witness from Rocq `Prop` existential into imported Lean `SProp Exists` is forbidden by Rocq's sort elimination rules. `PropSPropBridge.v` now isolates the minimal witness-transfer assumption `prop_sprop_trusted_exists_intro`; the existing reverse assumption remains `prop_sprop_trusted_elim`.
- `Print Assumptions exists_first_intermediate_point_statement_certificate` shows exactly those two explicit trust-boundary assumptions plus importer definitional UIP. Status: **CERTIFIED_WITH_PROP_SPROP_BRIDGE**. The official-source statement witness is closed; the imported statement witness lists the statement-only imported theorem constant, as expected.
- Machine-check command: `opam exec --switch=rocq93rc1 -- rocq c -R ~/.opam/prosa-0.6/.opam-switch/sources/rocq-prosa.0.6 prosa -Q /private/tmp/rocq-lean-import-93/src LeanImport -I /private/tmp/rocq-lean-import-93/src -Q generated_hard HardSource HardStepFunctionCertificate.v` (run from `Validation/rocq`; exit 0).

### 2026-09-19 14:59:29 HKT — recursive definition-to-theorem chain closed

- Added `HardNinRemAllCertificate.v`, adapting the reusable `seq ↔ List` roundtrip and membership construction/deconstruction pattern to the actual `List` representation in `HardCoreValidation.out`.
- Rocq kernel accepted `nin_rem_all_statement_certificate`. The proof composes the already-certified `rem_all_recursive_certificate` with bidirectional membership preservation; it does not invoke either the official `nin_rem_all` proof or the imported Lean theorem proof.
- `Print Assumptions` shows `prop_sprop_trusted_elim` plus importer definitional UIP. The source statement witness is closed, while the imported statement witness separately lists the statement-only imported theorem constant. Status: **CERTIFIED_WITH_PROP_SPROP_BRIDGE**.
- This closes the requested recursive chain: actual recursive definition `rem_all` (**CERTIFIED**) → dependent theorem statement `nin_rem_all` (**CERTIFIED_WITH_PROP_SPROP_BRIDGE**).

### 2026-09-19 15:06:01 HKT — big-operator target imported and parametrically certified

- The original 4.15 MB `big_nat_eq0` export recursively included proof bodies from transitive Mathlib dependencies. Rocq import terminated with exit 139 near the Omega/`UInt32` dependency path. This was an exporter/importer scalability failure, not a theorem mismatch.
- Generalized statement-only export with wildcard configuration: `HARD_ALL_THEOREMS_STATEMENT_ONLY=1` exports every transitive Lean theorem by its exact compiled type while still exporting ordinary definition bodies. This is configuration-driven and contains no theorem-name special case.
- Re-exported `big_nat_eq0` as a 7,301-line / 141,651-byte artifact, SHA-256 `2a9402d7202356eaed09c22553a776f2ea16ab5928567d5d62b4e218895518ab`. Rocq 9.3 imported it successfully in 2.7 seconds; the actual target type directly contains `Finset.sum`, `Finset.Ico`, `Iff`, `forall`, `And`, and Nat order.
- Added `HardSumCertificate.v` with reusable Nat/order/function representation and a compositional proof of the complete theorem proposition. Rocq kernel accepted `big_nat_eq0_parametric_certificate` against the actual imported declaration type.
- The result is **PARAMETRICALLY_CERTIFIED**, not fully closed: it has one explicit semantic premise, `FiniteNatSumValueBridge`, equating the actual imported `Finset.sum (Finset.Ico ...)` value with the MathComp interval big operator. This precisely identifies the next reusable bridge; no target-specific logical premise is hidden.
- `Print Assumptions` also exposes `prop_sprop_trusted_elim`, importer UIP, and theorem dependencies turned into statement-only axioms to keep the artifact importable. Consequently this result is not reported as fully `CERTIFIED`.
- Mutation test: `HardSumMutationTest.v` changes imported `sum = 0` to `sum = 1` and uses Rocq `Fail Definition` to verify that the original correspondence certificate is rejected. The mutation fixture compiles with exit 0, so mutation detection is **PASS**.

### 2026-09-19 15:08:02 HKT — repeatable Experiment 5 validator complete

- Added `scripts/validate_hard_translation.sh` and ran it end to end with exit 0. It performs configuration-driven multi-file source acquisition, source hashing, artifact presence checks, forbidden-proof-escape checks, importer compilation, certificate compilation, assumption printing, mutation testing, and final status output.
- The final run reports 6 / 9 challenge declarations validated and 3 / 9 failed because the declarations do not exist in the pinned official Prosa 0.6 source.
- Verified with `git diff -- Prosa` that the frozen production Lean translation was not modified.
- Correction to the early feasibility note at 13:28: a complete Rocq-9.3 compile of official `util/list.v` ultimately fails at a later unrelated legacy proof (`No applicable tactic`). The target-scoped automatically generated `util/list` module is what actually compiles and participates in the certificates. The source declaration blocks themselves remain byte-identical and hash-checked.

## Final machine-checked results

| Target | Actual Lean artifact imported? | Source acquisition | Correspondence | Assumptions / open dependency | Mutation | Status |
| --- | --- | --- | --- | --- | --- | --- |
| `Prosa.Util.Sum.big_nat_eq0` | yes | exact auto-extracted Prosa 0.6 block | complete logical proposition, parameterized by value relation | `FiniteNatSumValueBridge`; Prop/SProp elimination; statement-only dependency axioms | `sum = 1` rejected | **PARAMETRICALLY_CERTIFIED** |
| `Prosa.Util.Sum.sum_diff` | Lean exists | no v0.6 declaration exists | none possible | source provenance missing | n/a | **FAILED** |
| `Prosa.Util.Sum.sum_seq_gt0P` | Lean exists | no v0.6 declaration exists | none possible | source provenance missing | n/a | **FAILED** |
| `Prosa.Util.Sum.sum_pred_diff` | Lean exists | no v0.6 declaration exists | none possible | source provenance missing | n/a | **FAILED** |
| `Prosa.Util.List.rem_all` | yes | exact auto-extracted Prosa 0.6 block | recursive output equality under `seq ↔ List` | importer definitional UIP only | n/a | **CERTIFIED** |
| `Prosa.Util.List.nin_rem_all` | yes | exact auto-extracted Prosa 0.6 block | bidirectional theorem statement | `prop_sprop_trusted_elim`; importer UIP | n/a | **CERTIFIED_WITH_PROP_SPROP_BRIDGE** |
| `StepFunction.exists_first_intermediate_point` | yes | exact block from official `util/unit_growth.v` | bidirectional higher-order theorem statement | two isolated Prop/SProp bridges; importer UIP | n/a | **CERTIFIED_WITH_PROP_SPROP_BRIDGE** |
| Spin `processor_state` | yes | direct official import | constructor-level relation | none beyond importer foundation | n/a | **CERTIFIED** |
| `spin_scheduled_on` | yes | direct official import | exhaustive matcher preservation | importer definitional UIP only | n/a | **CERTIFIED** |

The three `FAILED` sum declarations are not demonstrated semantic formula mismatches. They are a precise 1:1 translation/provenance failure: the frozen Lean snapshot contains these names, but the pinned official Prosa 0.6 tree at `414e66760333eaa4ef78c685bcf53291c527a548` contains no corresponding Rocq declaration anywhere.

## Assumption and trust accounting

- `rem_all_recursive_certificate`: imported equality's definitional UIP only; no validation axiom.
- Spin constructor certificates: closed under the global context.
- `spin_scheduled_on_certificate`: imported equality/local truth definitional UIP only.
- `nin_rem_all_statement_certificate`: `prop_sprop_trusted_elim` plus importer UIP.
- `exists_first_intermediate_point_statement_certificate`: `prop_sprop_trusted_elim`, `prop_sprop_trusted_exists_intro`, and importer UIP. The second assumption is the isolated witness-transfer boundary required because Rocq forbids eliminating a `Prop` existential into imported Lean's witness-carrying `SProp Exists`.
- `big_nat_eq0_parametric_certificate`: its explicit argument `FiniteNatSumValueBridge` is not an axiom and therefore does not appear in `Print Assumptions`, but it remains an uncertified semantic dependency. In addition, `Print Assumptions` exposes the Prop/SProp eliminator and transitive Lean theorem types exported as axioms in the all-statements mode. This result is intentionally not classified as closed.
- Source declaration witnesses are closed under the global context. Imported theorem witnesses list the selected statement-only Lean theorem constants, demonstrating that the exact imported compiled types—not handwritten substitutes—are checked.

## Reusable bridge inventory

Nine reusable components were implemented or generalized in this experiment:

1. MathComp `eqType` to actual imported Lean `DecidableEq`, preserving Boolean equality.
2. MathComp `seq` to imported Lean `List`, with both roundtrips.
3. Bidirectional MathComp membership / imported `List.Mem` preservation.
4. Imported equality symmetry, transitivity, congruence, transport, and explicit-`Decidable` `ite` branch lemmas.
5. Rocq nat / imported Lean `Nat` conversion and roundtrips.
6. Compositional Nat `≤` and `<` preservation.
7. MathComp Bool truth and negation versus imported equality-to-`Bool.true`.
8. Higher-order pointwise predicate relation `StepPredRel`.
9. Isolated Prop/SProp truth and existential-witness trust boundary.

One important reusable bridge remains open: `FiniteNatSumValueBridge`, covering MathComp interval big operators versus the actual imported `Finset.sum (Finset.Ico ...)`. Closing it would upgrade `big_nat_eq0` from parameteric to a trust-accounted theorem certificate and would be the main enabler for a larger family of sum declarations.

## Answers to the challenge questions

1. **Big operators / sums:** the theorem's full logical structure is compositionally certifiable, actual artifact import now works, and mutation is detected. The numeric sum-value bridge itself is not yet dependency-closed, so the result is parameteric rather than fully certified.
2. **Recursive definitions:** yes. `rem_all` demonstrates correspondence between a source structural `Fixpoint` and Lean's imported `List.brecOn` course-of-values implementation without modifying the Lean translation.
3. **Higher-order functions / predicates:** they require a pointwise logical relation over related domains. `StepPredRel` was sufficient for the complex step-function theorem.
4. **Custom inductives:** yes. Constructor-level correspondence for `Idle`, `Spin`, and `Progress`, followed by exhaustive matcher preservation, is fully kernel-checked.
5. **Complex theorem propositions:** yes, with explicit sort-boundary accounting. The validator handles nested `∀`, `∃`, `∧`, implication, negation, and inequalities.
6. **Translation/provenance failures:** `sum_diff`, `sum_seq_gt0P`, and `sum_pred_diff` have no official Prosa 0.6 source declaration, so 1:1 validation fails before semantics.
7. **Validator limitations:** full Finset/MathComp interval-sum value correspondence remains open; the default proof-body export also exceeds the practical importer path and crashes, while generic all-theorem statement-only export succeeds but expands the assumption boundary.
8. **Bridges worth retaining:** Nat/order, Bool truth, higher-order predicate, seq/List membership, imported `ite`, and Prop/SProp existential accounting all already cover multiple proof branches or targets. The finite-sum value bridge is the highest-value next addition for scaling to 50–100 declarations.

## Reproduction

From `Prosa-fei/`:

```bash
# Reuse the recorded actual artifacts.
./Validation/scripts/validate_hard_translation.sh

# Rebuild all three actual Lean artifacts first, then validate.
REEXPORT=1 ./Validation/scripts/validate_hard_translation.sh
```

The successful recorded run is in `reports/logs/experiment5_validate_hard_translation_summary.log`. Individual importer, certificate, source-fidelity, assumption, and mutation outputs are under `reports/logs/`.

## Files added or materially changed

- `mapping/hard_validation_targets.yaml`
- `scripts/extract_rocq_declarations.py`
- `scripts/generate_rocq_source_modules.py`
- `scripts/export_hard_validation.sh`
- `scripts/validate_hard_translation.sh`
- `patches/lean4export-generic-statement-only.patch`
- `rocq/ImportedHardCore93.v`
- `rocq/ImportedExistsFirstIntermediatePoint93.v`
- `rocq/ImportedBigNatEq093.v`
- `rocq/HardCoreCertificates.v`
- `rocq/HardNinRemAllCertificate.v`
- `rocq/HardStepFunctionCertificate.v`
- `rocq/HardSumCertificate.v`
- `rocq/HardSumMutationTest.v`
- `rocq/PropSPropBridge.v`

No file under `Prosa/` was modified.

### 2026-09-19 15:09:57 HKT — clean rebuild-and-validate reproduction confirmed

- Ran `REEXPORT=1 ./Validation/scripts/validate_hard_translation.sh`; exit 0.
- This rebuilt all selected Lean artifacts from the frozen source before importing and recompiling every source module and certificate.
- Reproduced artifact SHA-256 values: `HardCoreValidation.out` = `b546b2257e12872d159afcdc1f4c6e64ae7678d7b5e4ea93bd73ad2400142b96`; `ExistsFirstIntermediatePoint.out` = `c3fb77511b70d968523d5e4ae51f3a1b7df26edf47f998a7a11fcfc32ccfe78c`; `BigNatEq0AllStatements.out` = `2a9402d7202356eaed09c22553a776f2ea16ab5928567d5d62b4e218895518ab`.
- `git diff --check` passed.
