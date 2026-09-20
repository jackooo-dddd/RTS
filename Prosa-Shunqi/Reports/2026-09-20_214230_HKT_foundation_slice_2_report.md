# FOUNDATION_SLICE_2 Report

Report started: **2026-09-20 21:42:30 HKT**.

This report is cumulative. Compilation alone never implies semantic acceptance.

## 2026-09-20 21:42:30 HKT — Infrastructure and selection

- A workspace-local authoritative source checkout was created at `Validation/.work/prosa-v06-414e667` from the official upstream repository.
- Commit `414e66760333eaa4ef78c685bcf53291c527a548`, tree `7d7e94c731f7eefde4ca738310d4cafdd7bebdf0`, remote URL, and clean status were verified fail-closed.
- `lean4export` was rebuilt locally from its pinned base plus the exact checked-in Slice 1 patch. Its binary hash is identical to Slice 1.
- The Slice 1 importer base commit `c9f43ad…` was found to be a non-upstream local commit and therefore not fetchable in a fresh clone. Reproducibility was repaired by pinning its reachable upstream parent `546979b…` and checking in the complete parent-to-current source delta, including UInt32 support and Rocq 9.3 compatibility changes.
- The locally rebuilt importer plugin and foundation `.vo` hashes are identical to Slice 1.
- Tooling status: `TOOLING_REPRODUCIBLE`.
- Selection was frozen before production translation in `foundation_slice_2_selection.json`.
- Selected Layer-0 files: `util/notation.v`, `util/tactics.v`, `util/rel.v`, `util/seqset.v`, `util/subadditivity.v`, and `util/supremum.v` (22 public declarations).
- `util/nat.v` remains conditional and may start only after `util/tactics.v` is accepted.
- `util/bigop.v` and `util/setoid.v` remain explicitly deferred.

Next: extract common fresh-build/import/audit infrastructure, then translate selected files whole-file in dependency-safe order.

## 2026-09-20 22:25:57 HKT — Clean end-to-end run completed

The reusable validator entry point is now:

```bash
cd Prosa-Shunqi
./Validation/scripts/validate_foundation_slice_2.sh
```

The final run used a new build directory
`Validation/.work/runs/foundation_slice_2.d29JTy`. It rebuilt every selected
Lean module, exported each declaration from the fresh `.olean`, compiled fresh
official-source validation copies, imported all six artifacts, compiled the
Rocq certificates, and ran fail-closed assumption classifiers. Canonical
artifacts were published only after all of these steps succeeded.

During hardening, an incorrect expected source-file SHA table was found. The
checkout itself was already pinned to the correct commit/tree and the executed
source bytes were official, but this exposed that naked shell tests were not a
sufficient fail-closed guard in this execution path. The table was corrected
to the actual full-file SHA-256 values and all source/toolchain/tool hashes now
use explicit error branches. The clean run above is the post-fix evidence.

### Fixed environment and evidence

- Rocq source commit: `414e66760333eaa4ef78c685bcf53291c527a548`
- Rocq source tree: `7d7e94c731f7eefde4ca738310d4cafdd7bebdf0`
- Lean: `4.33.1` (`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`)
- Mathlib: `0df444a360eaa60ab8c11dca51a86af692955474`
- Rocq: `9.3+rc1`
- lean4export binary SHA-256: `83b3b72e910b521347d0d9b9f457f097ae99d5cfc0570337721f7434295b98de`
- rocq-lean-import plugin SHA-256: `2ab657f4f558a95ecebd55b22583c02008cdef832ab41d6f63c6059e224648cf`
- importer foundation SHA-256: `05dd63bab81628b306e363edba53523e5f3e6f0ada73075db5fa220e245794b3`
- Tooling status: `TOOLING_REPRODUCIBLE`

The official checkout remained clean. Two patches were applied only to fresh
Rocq-9.3 validation copies: the obsolete `ssreflect.done` qualifier in
`util/tactics.v`, and a binder-syntax compatibility edit in `util/seqset.v`.
Neither changes a target declaration statement. Their SHA-256 values are
`efa0ded9e17a6de4f1f128b9a96301a64d71d53328d1654343693356dbaa746d`
and `7f3a189bf6d20ded3a3c0ad58b0046d011620cb177401bc45a5f14457bf8cdc2`.

### Translation and file gates

All 22 public declarations have production counterparts. All six production
modules compile from scratch, and every theorem/instance included in the Lean
proof audit passed `#print axioms`. The only Lean axioms reported were the
explicitly allowed standard `propext` uses; `sorryAx` and custom axioms were
absent.

| Source file | Public | Migration mix | Compile | Proof clean | Certified | File status |
| --- | ---: | --- | --- | --- | ---: | --- |
| `util/notation.v` | 1 | 1 new | PASS | PASS | 1 | `ACCEPTED_V06_FILE` |
| `util/tactics.v` | 2 | 1 adapt, 1 new | PASS | PASS | 1 | `PARTIAL_V06_FILE` |
| `util/rel.v` | 3 | 3 adapt | PASS | PASS | 1 | `PARTIAL_V06_FILE` |
| `util/seqset.v` | 3 | 2 reuse, 1 new | PASS | PASS | 0 | `PARTIAL_V06_FILE` |
| `util/subadditivity.v` | 6 | 6 new | PASS | PASS | 0 | `PARTIAL_V06_FILE` |
| `util/supremum.v` | 7 | 2 reuse, 5 adapt | PASS | PASS | 2 | `PARTIAL_V06_FILE` |

The complete migration totals are 4 `REUSE_AFTER_REVALIDATION`, 9
`ADAPT_OLD_LEAN`, and 9 `NEW_TRANSLATION`. No old file was copied wholesale.
`util/seqset.v` deliberately represents an ordered, duplicate-free sequence
as a `List` plus `Nodup`, not as a `Finset`, so its observable sequence order
is not silently erased. Its representation certificate remains open.

### Declaration matrix

| Official Rocq declaration | Production Lean declaration | Migration | Lean proof audit | Semantic status | Acceptance |
| --- | --- | --- | --- | --- | --- |
| `prosa.util.notation.constant` | `Prosa.Util.Notation.constant` | NEW_TRANSLATION | PASS | `CERTIFIED` | `ACCEPTED_V06_TRANSLATION` |
| `prosa.util.tactics.neqP` | `Prosa.Util.Tactics.neqP` | ADAPT_OLD_LEAN | PASS | `NOT_YET_VALIDATED` | `TRANSLATED_NOT_CERTIFIED` |
| `prosa.util.tactics.modusponens` | `Prosa.Util.Tactics.modusponens` | NEW_TRANSLATION | PASS | `CERTIFIED` | `ACCEPTED_V06_TRANSLATION` |
| `prosa.util.rel.monotone` | `Prosa.Util.Rel.monotone` | ADAPT_OLD_LEAN | PASS | `CERTIFIED` | `ACCEPTED_V06_TRANSLATION` |
| `prosa.util.rel.total_over_list` | `Prosa.Util.Rel.total_over_list` | ADAPT_OLD_LEAN | PASS | `NOT_YET_VALIDATED` | `TRANSLATED_NOT_CERTIFIED` |
| `prosa.util.rel.antisymmetric_over_list` | `Prosa.Util.Rel.antisymmetric_over_list` | ADAPT_OLD_LEAN | PASS | `NOT_YET_VALIDATED` | `TRANSLATED_NOT_CERTIFIED` |
| `prosa.util.seqset.set` | `Prosa.Util.Seqset.set` | NEW_TRANSLATION | PASS | `NOT_YET_VALIDATED` | `TRANSLATED_NOT_CERTIFIED` |
| `prosa.util.seqset.set_of` | `Prosa.Util.Seqset.set_of` | REUSE_AFTER_REVALIDATION | PASS | `NOT_YET_VALIDATED` | `TRANSLATED_NOT_CERTIFIED` |
| `prosa.util.seqset.set_uniq` | `Prosa.Util.Seqset.set_uniq` | REUSE_AFTER_REVALIDATION | PASS | `NOT_YET_VALIDATED` | `TRANSLATED_NOT_CERTIFIED` |
| `prosa.util.subadditivity.subadditive_at` | `Prosa.Util.Subadditivity.subadditive_at` | NEW_TRANSLATION | PASS | `NOT_YET_VALIDATED` | `TRANSLATED_NOT_CERTIFIED` |
| `prosa.util.subadditivity.subadditive_until` | `Prosa.Util.Subadditivity.subadditive_until` | NEW_TRANSLATION | PASS | `NOT_YET_VALIDATED` | `TRANSLATED_NOT_CERTIFIED` |
| `prosa.util.subadditivity.subadditive` | `Prosa.Util.Subadditivity.subadditive` | NEW_TRANSLATION | PASS | `NOT_YET_VALIDATED` | `TRANSLATED_NOT_CERTIFIED` |
| `prosa.util.subadditivity.subadditive_standard` | `Prosa.Util.Subadditivity.subadditive_standard` | NEW_TRANSLATION | PASS | `NOT_YET_VALIDATED` | `TRANSLATED_NOT_CERTIFIED` |
| `prosa.util.subadditivity.subadditive_standard_equivalence` | `Prosa.Util.Subadditivity.subadditive_standard_equivalence` | NEW_TRANSLATION | PASS | `NOT_YET_VALIDATED` | `TRANSLATED_NOT_CERTIFIED` |
| `prosa.util.subadditivity.subadditive_leq_mul` | `Prosa.Util.Subadditivity.subadditive_leq_mul` | NEW_TRANSLATION | PASS | `NOT_YET_VALIDATED` | `TRANSLATED_NOT_CERTIFIED` |
| `prosa.util.supremum.choose_superior` | `Prosa.Util.Supremum.choose_superior` | REUSE_AFTER_REVALIDATION | PASS | `CERTIFIED` | `ACCEPTED_V06_TRANSLATION` |
| `prosa.util.supremum.supremum` | `Prosa.Util.Supremum.supremum` | REUSE_AFTER_REVALIDATION | PASS | `CERTIFIED` | `ACCEPTED_V06_TRANSLATION` |
| `prosa.util.supremum.supremum_unfold` | `Prosa.Util.Supremum.supremum_unfold` | ADAPT_OLD_LEAN | PASS | `NOT_YET_VALIDATED` | `TRANSLATED_NOT_CERTIFIED` |
| `prosa.util.supremum.supremum_exists` | `Prosa.Util.Supremum.supremum_exists` | ADAPT_OLD_LEAN | PASS | `NOT_YET_VALIDATED` | `TRANSLATED_NOT_CERTIFIED` |
| `prosa.util.supremum.supremum_none` | `Prosa.Util.Supremum.supremum_none` | ADAPT_OLD_LEAN | PASS | `NOT_YET_VALIDATED` | `TRANSLATED_NOT_CERTIFIED` |
| `prosa.util.supremum.supremum_in` | `Prosa.Util.Supremum.supremum_in` | ADAPT_OLD_LEAN | PASS | `NOT_YET_VALIDATED` | `TRANSLATED_NOT_CERTIFIED` |
| `prosa.util.supremum.supremum_spec` | `Prosa.Util.Supremum.supremum_spec` | ADAPT_OLD_LEAN | PASS | `NOT_YET_VALIDATED` | `TRANSLATED_NOT_CERTIFIED` |

### Machine-checked semantic results

The following certificates were accepted by the Rocq kernel against actual
freshly imported Lean artifacts:

- `constant_value_certificate`
- `modusponens_statement_certificate`
- `monotone_correspondence_certificate`
- `choose_superior_correspondence_certificate`
- `supremum_correspondence_certificate`

The assumption audit reports no semantic premise, no target-theorem
self-dependency, and no unexpected assumption for all five. `constant` and
`modusponens` are closed under the global context. `monotone`,
`choose_superior`, and `supremum` expose only the exact imported equality
foundation (`Lean.eq`); the latter two also expose the locally defined
proof-irrelevant SProp witness `SupValidationTrue` as definitional UIP. None of
the five uses `PropSPropFoundation.interpret_strict`, so their status remains
`CERTIFIED`, not `CERTIFIED_WITH_PROP_SPROP_FOUNDATION`.

For the accepted theorem `modusponens`, two additional Rocq-kernel type guards
check that the independently related source/target logical shells are exactly
the elaborated types of `prosa.util.tactics.modusponens` and the imported
`Prosa_Util_Tactics_modusponens`. The correspondence certificate itself does
not depend on either theorem proof constant, preserving the self-dependency
check.

The remaining 17 declarations are deliberately `NOT_YET_VALIDATED`, not
`FAILED`: their production declarations compile and are proof-clean, but the
required equality/reflection, List membership, sequence-set representation,
Nat arithmetic, or theorem-shell semantic bridges have not yet been closed.
No claim of semantic equivalence is made for them.

Fresh export SHA-256 values:

| Module | Export SHA-256 |
| --- | --- |
| Notation | `310e9e71641fcdc2d92c2f499802efa7b7d764ce63a76c0190f772ab80b70de3` |
| Tactics | `34140e14c5508cedba1b3e5849c89b51e5ce81c8152f3a161d065bfcfaeafadb` |
| Rel | `4c6834a8cecfaacd3a19bb34ad2897b9952010205cb59548dccb854c6d67f040` |
| Seqset | `94b6b6e9bddef0fd300e1638ac929dce1c1fdbd6a3e605c037f22917afeac00a` |
| Subadditivity | `9ca38bbffc3c1b052bb60aa3a2a091fd15aeb531f195124c604f970ca8243b50` |
| Supremum | `543a901e763477faab3198bbb12e12acf11fd51cbfe68114dc048897ce2b5d76` |

All per-declaration source command hashes, elaborated source type
fingerprints, Lean elaborated types, type/body hashes, fresh `.olean`, export,
import, certificate, and invalidation hashes are in
`Validation/planning/v06_pipeline/foundation_slice_2_manifest.json`.

### Coverage and integrity

- Slice 2 attempted: 6 files / 22 declarations.
- Slice 2 accepted: 1 whole file / 5 declarations.
- Slice 2 partial: 5 files / 17 translated-but-not-certified declarations.
- Cumulative accepted production coverage: **2 / 357 files**, **7 / 2439 declarations**.
- Slice 2 proof-clean declarations: **22 / 22**.
- Deferred CoqEAL boundary remains: **239 declarations**.
- `Prosa-fei/Prosa/`: unchanged.
- `Prosa/Behavior/Time.lean` and Slice 1 accepted result: unchanged.
- Accepted v0.6 dependency/mapping snapshots: unchanged.
- Workspace-local pinned source: clean and exact.
- `lake build`: PASS under Lean 4.33.1 / pinned Mathlib.
- `git diff --check`: PASS.

`util/nat.v` was not started because its authoritative file dependency
`util/tactics.v` has not yet reached `ACCEPTED_V06_FILE`.

## Final verdict

```text
FOUNDATION_SLICE_2_STATUS = PARTIAL
READY_FOR_JOB_FOUNDATION = NO
```

The immediate readiness blocker is semantic closure, not Lean compilation:
`neqP`, the two list-relation definitions, the complete `seqset`
representation, the six subadditivity declarations, and five supremum theorem
statements still need actual-artifact correspondence certificates. No
`behavior/job.v`, `ProcessorState`, or higher layer translation was started.
