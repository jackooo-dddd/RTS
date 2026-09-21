# UTILITY_FOUNDATION_EXPANSION Report

Report started: **2026-09-21 08:22:58 HKT**.

This report is cumulative. Compilation alone never counts as semantic
acceptance. Progress, failed attempts, blockers, and machine-checked results
are appended as they occur.

## 2026-09-21 08:22:58 HKT — authoritative selection audit started

- Authoritative source: Prosa v0.6 commit
  `414e66760333eaa4ef78c685bcf53291c527a548`.
- Target environment: Lean 4.33.1 and Mathlib
  `0df444a360eaa60ab8c11dca51a86af692955474`.
- Frozen baseline: 7 accepted files, 24 accepted declarations, and zero
  translated-but-uncertified declarations.
- The dependency inventory confirms exactly 104 targets:
  `util/nat.v` (2), `util/unit_growth.v` (12), `util/search_arg.v` (8),
  `util/list.v` (57), and `util/sum.v` (25).
- Initial file-DAG readiness:
  - ready: `util/nat.v`, `util/unit_growth.v`, `util/search_arg.v`,
    `util/list.v`;
  - deferred: `util/sum.v`, until `util/nat.v` is an accepted file.
- Migration evidence across the 104 rows, mechanically recomputed from the
  accepted migration table: `REUSE_AFTER_REVALIDATION=7`,
  `ADAPT_OLD_LEAN=46`, `NEW_TRANSLATION=49`, and `REVIEW_REQUIRED=2`.
- The two review-required declarations are `leq_sum_sub_uniq` and
  `reorder_summation`. They remain explicit review gates and are not treated
  as trusted reuse candidates.
- No production or historical Lean file was modified during this selection
  audit.

The generated selection snapshot lists all 104 declarations with source
order, elaborated type evidence, migration action, representation boundary,
validation class, and file-DAG readiness.

## 2026-09-21 08:29:34 HKT — `util/nat.v` production translation compiles

- Added the complete two-declaration v0.6 translation in
  `Prosa/Util/Nat.lean`: `subnACA` and `leq_subRL_impl`.
- Both statements follow the authoritative elaborated types, including
  implicit Nat binders and truncated Nat subtraction; neither theorem was
  copied from the historical file, whose names and inventory differ.
- Direct Lean checking passed, and `lake build Prosa.Util.Nat` produced the
  project artifact successfully.
- The first audit-fixture attempt correctly failed because direct `lean` type
  checking had not installed a Lake `.olean`. Rebuilding the module through
  Lake fixed this infrastructure issue; it was not a theorem proof failure.
- `#print axioms` reports only the currently allowed standard Lean proof
  foundations `propext` and `Quot.sound` for both omega-derived proofs. There
  is no `sorryAx` or custom axiom.
- Status remains `TRANSLATED_NOT_CERTIFIED`: actual-artifact export/import,
  the reusable truncated-subtraction bridge, Rocq correspondence proofs, and
  fail-closed assumption audit are still required before acceptance.

## 2026-09-21 09:33:00 HKT — Nat subtraction and theorem certificates compiled

- Fresh `Nat.olean` export and `rocq-lean-import` succeeded for the two exact
  compiled theorem types in statement-only mode.
- The first fresh probe failed before export because `Nat.lean` imports the
  frozen `Tactics.lean` but the isolated build directory did not yet contain
  `Tactics.olean`. The retry compiled that dependency first and succeeded;
  no stale project `.olean` was used.
- Added reusable `NatSubCorrespondence.v`. It proves the actual imported
  Lean `Nat.sub` computation equations, relates its course-of-values
  implementation to iterated predecessor, and then to MathComp truncated
  subtraction.
- Separate audited lemmas cover both branches:
  - non-truncated input `b <= a`;
  - truncated input `a < b`, with output zero.
- Added compositional theorem certificates for `subnACA` and
  `leq_subRL_impl`. Their semantic proofs use Nat addition, order, equality,
  and the new subtraction bridge. They do not invoke either official source
  proof or imported target theorem constant; those constants occur only in
  separate exact-type guards.
- Preliminary `Print Assumptions` showed only imported equality
  definitional-UIP, the approved `interpret_strict` foundation, and the
  already audited Nat truth singleton. The fail-closed classifier initially
  rejected the fully qualified spelling
  `SubadditivityNatCorrespondence.SubNatTrue`; the exact name was added to the
  existing definitional-UIP allowlist. No prefix rule or new trust category
  was introduced.

## 2026-09-21 09:42:13 HKT — `util/nat.v` accepted end to end

- A new isolated run directory rebuilt `Prosa.Util.Tactics` and
  `Prosa.Util.Nat`; no project `.olean` was used to satisfy those imports.
- The generic statement-only exporter read both exact theorem types from the
  fresh `Nat.olean`. `rocq-lean-import` then imported the resulting
  `Nat.out`, and Rocq 9.3 compiled both the official source and the semantic
  certificates.
- The official `util/nat.v` validation copy is byte-identical to the pinned
  source (`SHA-256 6f1c4f84...b80`). Only the already-audited tactic-only
  Rocq-9.3 compatibility patch was applied to its prerequisite
  `util/tactics.v`.
- `subnACA` and `leq_subRL_impl` are both
  `CERTIFIED_WITH_PROP_SPROP_FOUNDATION`. For both certificates:
  semantic premises are empty, source-theorem dependency is false,
  target-theorem dependency is false, and unexpected assumptions are empty.
- The reusable subtraction results themselves are `CERTIFIED`; their only
  recorded foundation is the imported equality representation. The theorem
  statements additionally use the existing
  `PropSPropFoundation.interpret_strict` boundary.
- Lean `#print axioms` passed with only the exact allowed standard
  foundations `propext` and `Quot.sound`; no `sorryAx` or custom axiom was
  present.
- Fresh artifact hashes include:
  `Nat.olean c1591f70...4f21`, `Nat.out eba900fd...8ecb`, and imported
  `ImportedNat.vo 322b5102...34d6`.
- Frozen-baseline audit passed both before and after the run. The 24 prior
  declarations and both planning snapshots were unchanged.
- Status: `util/nat.v = ACCEPTED_V06_FILE` (2/2). Cumulative coverage is now
  8/357 accepted files and 26/2439 accepted declarations, with zero
  translated-but-uncertified declarations. The file-DAG prerequisite for
  `util/sum.v` is now satisfied.

## 2026-09-21 09:48:25 HKT — `util/search_arg.v` translated and proof-clean

- Added a whole-file production candidate containing exactly the eight v0.6
  public declarations. The v0.6-only
  `earliest_pred_element_exists_case` was translated from the authoritative
  source; the seven historical candidates were reviewed against the v0.6
  statements, and the historical Lean-only `ex_minn_le_ex` was not copied.
- `search_arg` retains the source's recursive right-to-left search over
  `[a,b)`, with `Option Nat`, Boolean predicate/order observations, and no
  `Finset` reformulation.
- `search_arg_none` exposes Boolean falsity directly as `P (f x) = false`;
  this preserves the source `~~ P (f x)` observation rather than silently
  turning the translated API into an unrelated predicate.
- `prop_on_ex_minn` no longer carries the historical extra
  `DecidablePred` parameter: decidability follows from its Boolean predicate,
  matching the v0.6 boundary more closely.
- Lean compilation passed for all eight declarations. The fail-closed
  `#print axioms` audit passed: `prop_on_ex_minn` is axiom-free;
  `search_arg_pred` uses `propext`; the remaining proof terms use an exact
  audited subset of `propext`, `Quot.sound`, and `Classical.choice`. There is
  no `sorryAx` or custom axiom.
- Current status is still `TRANSLATED_NOT_CERTIFIED` for 8 declarations.
  Fresh actual-artifact export/import, the operational `search_arg`
  correspondence, theorem-statement certificates, and Rocq assumption audit
  remain before this file can be accepted.

## 2026-09-21 10:17:56 HKT — `search_arg` artifact/source acquisition hardened; operational proof remains

- A fresh isolated `SearchArg.olean` was exported. The artifact contains the
  actual recursive `search_arg` body, exact statement-only types for all seven
  public lemmas, and both compiler-generated recursion equations with their
  kernel-checked `rfl` proof bodies. `rocq-lean-import` accepted the artifact.
- The imported equation proofs do not introduce theorem axioms. Their current
  `Print Assumptions` output contains only importer equality/HEq/True
  definitional-UIP foundations; it does not list either equation as an
  assumption.
- Direct compilation of the unchanged official `util/search_arg.v` under Rocq
  9.3 reaches the legacy theorem proofs but hits stack overflow in old
  ssreflect automation. Rocq `-vos` was tested and does not solve this because
  the old proof scripts are still elaborated.
- A proof-independent, configuration-driven source extractor was added. It
  copies computational blocks byte-for-byte and converts each exact official
  theorem header into a Prop-valued source statement definition, omitting the
  opaque proof without generating `Axiom`, `Admitted`, or a replacement proof.
  It records source file/block/statement hashes and reconstructed Section
  context. The extracted `search_arg` source module compiles under Rocq 9.3.
- An automatically recorded local notation reconnects the Section-closed
  extracted `search_arg` body to subsequent exact statement texts. This is a
  definitional binding, not a semantic premise; it is explicit in extraction
  metadata.
- The remaining hard step is the operational relation between MathComp's
  recursive `search_arg` and the actual imported Lean course-of-values
  recursion. The imported `rfl` equations provide a much smaller computation
  interface, but the proof still needs reusable `Option`, `Bool`, Nat-order,
  and higher-order function relations. Until that proof and the seven
  compositional statement certificates pass, all 8 declarations remain
  `TRANSLATED_NOT_CERTIFIED`; no false acceptance has been recorded.

## 2026-09-21 10:26:58 HKT — `util/unit_growth.v` translated and proof-clean

- Added the complete production candidate `Prosa/Util/UnitGrowth.lean` with
  all 12 public v0.6 declarations. Ten declarations are new in v0.6; the two
  intermediate-point lemmas were adapted from the historically related
  `util/step_function.v` implementation only after checking their v0.6 types.
- The recursive `slowed` definition retains the authoritative computation:
  `slowed F 0 = F 0` and
  `slowed F (n+1) = min (F (n+1)) (slowed F n + 1)`.
- The source `monotone leq` boundary remains an explicit Boolean relation via
  `Prosa.Util.Rel.monotone (fun x y => decide (x ≤ y))`; it was not silently
  replaced by an unrelated surface API.
- Lean compilation passed for all 12 declarations. The fail-closed
  `#print axioms` classifier passed for every theorem: the exact observed
  assumptions are subsets of `propext`, `Quot.sound`, and
  `Classical.choice`; there is no `sorryAx` or custom axiom.
- Current hashes are production source `5ada621c...a5c`, preliminary compiled
  artifact `b310d8a8...b92`, and axiom-audit summary `95661c86...249`.
  These are preliminary, not acceptance hashes; a fresh isolated build will
  replace the `.olean` hash during semantic validation.
- Current status is `TRANSLATED_NOT_CERTIFIED` for 12 declarations. Actual
  artifact export/import, operational correspondence for `slowed`, theorem
  statement certificates, and Rocq assumption audits remain. No declaration
  has been added to accepted coverage at this stage.

## 2026-09-21 10:46:29 HKT — source closure hardened and bridge inventory audited

- The source extractor was extended to consume the already verified
  `Check @declaration` evidence. This fixes an important Section-closure
  issue: a theorem header can omit hypotheses that appear in its final
  post-Section type because those hypotheses are used by the proof. The
  generated UnitGrowth source signatures now contain the full elaborated
  v0.6 types while retaining hashes of the exact source headers.
- Fresh `UnitGrowth.olean` export and `rocq-lean-import` succeeded. The
  artifact includes the two actual compiled definition bodies, exact
  statement-only types for ten theorems, and kernel-checked bodies for the
  two recursive `slowed` equations. Current probe hashes are
  `UnitGrowth.out 998976a4...094` and imported
  `ImportedUnitGrowth.vo 741c7b7b...512`.
- The already accepted common library contains 8 machine-checked bridge
  modules. Using the conservative public-bridge naming audit, these contain
  30 correspondence/canonical/roundtrip lemmas (45 lemmas total, including
  internal support results). Seven module families are intended for reuse;
  one (`SupremumTheoremCorrespondence`) is primarily a target-specific
  adapter. The seven reusable families expose 22 named bridge lemmas plus
  the Prop/SProp and logical-relation combinators.
- `UnitGrowthCorrespondence.v` is a ninth, in-progress module and is not
  included in those accepted counts. Nat `+`, `<=`, `<`, equality,
  Boolean-decision reflection, `unit_growth_function`, and Boolean
  monotonicity portions now elaborate; the current unresolved proof point is
  the final normalization step in the recursive `slowed` correspondence.
  A nonterminating broad `rewrite -!addn1` attempt was interrupted and is not
  accepted evidence. No UnitGrowth semantic status has been upgraded.

## 2026-09-21 10:57:43 HKT — UnitGrowth semantic proof coverage reaches 11 / 12

- `UnitGrowthCorrespondence.v` now compiles under Rocq 9.3, including the
  operational correspondence for the actual imported recursive `slowed`
  definition. The proof uses the imported, kernel-checked `slowed.eq_1` and
  `slowed.eq_2` computation equations rather than a hand-written Lean-side
  model.
- `UnitGrowthCertificate.v` now compiles semantic certificates for both
  computational definitions and nine of the ten theorem statements. Thus
  11 / 12 declarations in `util/unit_growth.v` have Rocq-kernel-checked proof
  bodies at this intermediate stage. The only remaining declaration is
  `exists_first_intermediate_point`.
- The observed `Print Assumptions` output contains the importer definitional
  UIP foundations and `PropSPropFoundation.interpret_strict`; no
  validation-specific semantic premise is visible. The fail-closed automatic
  assumption classifier and final content-addressed publication have not yet
  run, so these 11 declarations are **not yet counted as accepted**.
- Current layered progress for the 104-declaration main scope is therefore:
  22 translated and Lean proof-clean; 13 with a compiling Rocq semantic proof
  (the 2 accepted Nat declarations plus 11 preliminary UnitGrowth results);
  and 2 fully accepted after the complete audit/publication gate.
