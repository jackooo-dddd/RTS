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

## 2026-09-21 11:23:55 HKT — UnitGrowth reaches 12 / 12 semantic proof bodies

- Added the missing compositional certificate for
  `exists_first_intermediate_point`. It connects the exact pinned-source
  Boolean interval statement to the actual imported compiled Lean theorem
  type, including related predicates, Boolean `false`/`true`, strict and
  non-strict Nat bounds, the first-witness universal condition, and the
  existential witness.
- The source guard is definitionally equal to the extractor's exact
  post-Section v0.6 type. In particular it retains MathComp Boolean
  conjunctions rather than replacing them with an untracked Prop model.
- `UnitGrowthCorrespondence.v` and `UnitGrowthCertificate.v` both compile
  under Rocq 9.3. All 12 / 12 UnitGrowth declarations now have compiling
  semantic proof bodies. The new proof uses no target theorem proof, source
  theorem proof, validation-specific premise, `Admitted`, or new axiom.
- Current certificate-source hashes are
  `UnitGrowthCorrespondence.v 8ceb5a02...49f5` and
  `UnitGrowthCertificate.v 668cf5f9...9fd1`. These are still intermediate
  hashes: UnitGrowth is not marked accepted until a new isolated build,
  export/import, automatic assumption audit, baseline audit, and publication
  all pass.

## 2026-09-21 11:35:41 HKT — `util/unit_growth.v` accepted 12 / 12

- The complete fresh pipeline passed from a new isolated work directory:
  Lean dependency rebuild, UnitGrowth rebuild, proof/axiom audit, actual
  `lean4export`, `rocq-lean-import`, source-signature acquisition, all common
  bridge and certificate compilations, fail-closed `Print Assumptions`
  classification, frozen-baseline audit, content-addressed publication, and
  `git diff --check`.
- All 12 declarations are now `ACCEPTED_V06_TRANSLATION`; the whole source
  file is `ACCEPTED_V06_FILE`. All 12 have status
  `CERTIFIED_WITH_PROP_SPROP_FOUNDATION`. For every declaration:
  `semantic_premises = []`, target theorem dependency is false, source theorem
  dependency is false, and unexpected assumptions are empty.
- The only non-importer logical boundary is the existing audited
  `PropSPropFoundation.interpret_strict`; no new semantic axiom was introduced.
  The two imported recursive equation proofs for `slowed` were independently
  Lean-audited as axiom-free.
- Final fresh hashes include `.olean b08ffde3...5a20`, export
  `998976a4...109`, imported `.vo 741c7b7b...512`, generated source-signature
  `.vo 7d0622a3...437`, and source-acquisition metadata
  `9dc76085...87e`.
- Cumulative accepted coverage is now 9 / 357 files and 38 / 2439 public
  declarations. Within the current 104-declaration batch, 14 are accepted.

## 2026-09-21 11:38:31 HKT — incremental status model corrected

- The aggregate generator now consumes both fully accepted cluster evidence
  and explicit in-progress evidence. It distinguishes `NOT_STARTED`,
  `TRANSLATED`, `PROOF_CLEAN`, `SEMANTIC_PROOF_COMPILED`,
  `BLOCKED_SEMANTIC_VALIDATION`, and accepted results instead of treating every
  non-accepted file as not started.
- `util/unit_growth.v` is correctly shown as 12 translated, 12 proof-clean,
  12 semantic-proof-compiled, and 12 accepted.
- `util/search_arg.v` is correctly shown as 8 translated and 8 proof-clean,
  with 0 accepted and semantic validation still pending. Its fresh `.olean`,
  export, imported `.vo`, and generated source-signature hashes are bound in
  the progress record; this is not an acceptance claim.
- Current batch truth is 22 translated/proof-clean, 14 accepted, and 8
  translated-but-not-certified. Repository cache policy now ignores Python
  bytecode and `.lia.cache`; the existing generated `__pycache__` was removed.
  `git diff --check` passes.

## 2026-09-21 11:55:21 HKT — repository skill installed; SearchArg recursion bridge compiles

- Installed the user-supplied `prosa-v06-translation` repository skill at
  `.agents/skills/prosa-v06-translation/`. All 9 installed files are
  byte-identical to the supplied package. The original package remains in
  place, and no `AGENTS.md` was overwritten.
- Re-read the current utility manifest, status, approved representation
  policy, and foundational decisions before continuing. The current truth is
  9 / 357 accepted files and 38 / 2439 accepted declarations; this paragraph
  does not infer acceptance from file existence.
- SearchArg recovery approach 1 succeeded at the computational-definition
  level. `search_arg_definition_certificate` uses the actual imported
  `search_arg_eq_1` and `search_arg_eq_2` equations, induction on `b`, and
  canonical Nat/Bool/Option maps. It does not inspect the generated
  `Nat_brecOn` / `Nat_below` body.
- Rocq 9.3 compiled the certificate. `Print Assumptions` currently reports
  importer definitional-UIP foundations and the already-audited
  `PropSPropFoundation.interpret_strict`; no new semantic axiom was added.
  This is intermediate `SEMANTIC_PROOF_COMPILED` evidence for the `search_arg`
  Fixpoint only. The seven theorem statement certificates and the complete
  fail-closed publication audit remain open, so `util/search_arg.v` is not yet
  accepted.

## 2026-09-21 12:00:20 HKT — List and Sum starter clusters compile

- Started `util/list.v` without waiting for the remaining SearchArg theorem
  certificates. The first source-ordered cluster now has production candidates
  for `max0`, `first0`, and `last0` (3 / 57). Their actual compiled interfaces
  are respectively `List Nat -> Nat` with bodies `List.foldl Nat.max 0`,
  `List.headD 0`, and `List.getLastD 0`. Lean reports no axioms for these three
  computational definitions.
- Started `util/sum.v` because the authoritative file-DAG prerequisite
  `util/nat.v` is accepted. The requested starter cluster now has production
  candidates for `sum_of_ones`, `big_nat_eq0`, and
  `sum_le_summation_range` (3 / 25), using the approved half-open
  `Finset.Ico` representation.
- Both production modules compile under pinned Lean 4.33.1 / Mathlib. The Sum
  theorem proof audit reports only the currently allowed Lean foundations
  `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx` or custom axiom
  appears. These are compilation/proof-clean results, not semantic acceptance.
- Current workflow totals are 28 translated and proof-clean declarations, 14
  fully accepted declarations, and one additional SearchArg declaration with
  an intermediate compiling semantic proof. Cumulative accepted coverage
  remains 9 / 357 files and 38 / 2439 declarations until fresh artifact
  validation and assumption audits pass.

## 2026-09-21 12:14:28 HKT — List simple-definition certificates compile

- Added semantic certificates for the source-ordered `util/list.v` starter
  cluster: `max0`, `first0`, and `last0`. They refer directly to the actual
  declarations imported from the fresh compiled `Prosa.Util.List` artifact.
- Before proving correspondence, inspected the imported computational
  interface. The target artifact contains a monomorphic exported list carrier
  distinct from the generic support carrier, so the proof deliberately maps
  MathComp sequences to the exact `List_inst1 Nat` used by the three target
  declarations. It does not apply generic list equations to the wrong carrier.
- Kernel reduction establishes the actual monomorphic `foldl`, `headD`, and
  `getLastD` equations needed by the proof. The `max0` proof additionally
  connects MathComp `maxn` with the actual imported `Nat.max` decision tree.
- Rocq 9.3 compiled all three certificates. The fail-closed probe audit
  classifies `first0` and `last0` as `CERTIFIED` with importer equality
  foundations only, and `max0` as
  `CERTIFIED_WITH_PROP_SPROP_FOUNDATION` because its imported Nat-order
  branch uses the existing `interpret_strict` boundary. Semantic premises,
  source/target theorem dependencies, and unexpected assumptions are empty.
- This remains pre-publication evidence: a complete new isolated rebuild,
  source acquisition, export/import, baseline check, artifact hashing, and
  publication run is still required before these three are counted as
  accepted.

## 2026-09-21 12:18:24 HKT — List starter cluster accepted 3 / 57

- The new reusable entry point
  `Validation/scripts/validate_utility_list_simple.sh` completed from a new
  isolated work directory. It rebuilt the Lean dependency path, exported the
  three actual compiled bodies, automatically extracted the exact pinned-v0.6
  source bodies, imported the artifact into Rocq, compiled the certificates,
  ran the fail-closed assumption classifier and baseline audit, and published
  content-addressed evidence only after all gates passed.
- `max0`, `first0`, and `last0` are now individually
  `ACCEPTED_V06_TRANSLATION`. `first0` and `last0` are `CERTIFIED`; `max0` is
  `CERTIFIED_WITH_PROP_SPROP_FOUNDATION`. All three have no semantic premise,
  no source/target theorem dependency, and no unexpected assumption.
- Fresh hashes include `.olean 0991e257...f79e`, export
  `033db5ef...dd8e`, imported `.vo c35b1066...5156`, and generated official
  source `.vo 5959f59e...be2b`.
- The file remains `PARTIAL_V06_FILE`, correctly: only 3 of its 57 public
  declarations have been translated and accepted. Cumulative accepted
  declaration coverage rises from 38 to 41 / 2439; accepted whole-file
  coverage remains 9 / 357. Current translated-but-not-certified debt is 11
  declarations (8 SearchArg plus 3 Sum).

## 2026-09-21 12:39:32 HKT — Sum interval cluster accepted 3 / 25

- The workspace-local entry point
  `Validation/scripts/validate_utility_sum_interval.sh` completed from the new
  isolated work directory `Validation/.work/runs/utility_sum_interval.VJUeQ1`.
  It freshly rebuilt the dependency path and `Prosa.Util.Sum`, audited the
  Lean proofs, kernel-checked target-type normalization, exported the actual
  artifact, automatically extracted the pinned-v0.6 source statements,
  imported the result into Rocq, compiled the semantic certificates, and ran
  the fail-closed assumption and baseline audits before publication.
- `sum_of_ones`, `big_nat_eq0`, and `sum_le_summation_range` are now
  individually `ACCEPTED_V06_TRANSLATION`, all with status
  `CERTIFIED_WITH_PROP_SPROP_FOUNDATION`. Their certificates have no semantic
  premises, no source theorem dependency, no target theorem dependency, and no
  unexpected assumptions. The visible trust boundary is
  `PropSPropFoundation.interpret_strict` plus the importer equality foundation;
  `SubNatTrue` is classified as Rocq/SProp definitional UIP rather than a new
  semantic premise.
- The reusable `SumIntervalCorrespondence.v` bridge proves the value
  correspondence between MathComp's half-open interval big sum and the actual
  imported Lean `List.range'`/`map`/`foldr` computation obtained from
  `Finset.sum (Finset.Ico ...)`. It preserves the exact `[m,n)` endpoints,
  ordering and multiplicity, and its own audit is `CERTIFIED`.
- Each normalized theorem type is tied to this build's exact compiled theorem
  type by a Lean-kernel-checked equality guard in addition to the exporter
  `Meta.isDefEq` check. A validation-only mutation changing the fold identity
  from `0` to `1` was rejected with the expected definitional-equality failure.
- Fresh hashes are `.olean a3709f82...63f2`, export
  `1d05393f...bd6`, imported `.vo 8809b61c...4a36`, and generated source
  `.vo 1f861ee3...e59`; the machine-readable manifest contains the full exact
  values.
- `util/sum.v` remains `PARTIAL_V06_FILE` because 22 declarations remain.
  Cumulative accepted coverage is now 9 / 357 whole files and 44 / 2439
  declarations. Current translated-but-not-certified debt falls to 8, all in
  `util/search_arg.v`; List and Sum have no translated-but-uncertified starter
  declaration.

## 2026-09-21 12:56:22 HKT — SearchArg compositional statement route advances

- The second bounded SearchArg approach now compiles four compositional Rocq
  statement correspondences: `search_arg_none`, `search_arg_not_none`,
  `search_arg_pred`, and `search_arg_in_range`. They reuse the previously
  compiled actual-artifact recursion certificate based on imported
  `search_arg_eq_1` / `search_arg_eq_2`; no `Nat_brecOn` or `Nat_below` body is
  unfolded.
- The shared proof layer constructed once in
  `SearchArgStatementCertificate.v` covers canonical Nat transport, imported
  Bool truth/false observations, Option constructor/equality transport,
  conjunction, iff, Nat-indexed forall/exists, and half-open range predicates.
  All four theorem bodies reuse these relations rather than independently
  reproving the recursive computation.
- This is still intermediate `SEMANTIC_PROOF_COMPILED` evidence, not
  acceptance. Exact official-source/full-target type guards, a fresh isolated
  export/import, fail-closed assumption audit, and publication remain open.
  `earliest_pred_element_exists_case`, `search_arg_extremum`, and the
  proof-dependent `prop_on_ex_minn` remain to be handled.
- Reuse inventory at this point contains 10 independently maintained common
  bridge/foundation modules. Six are strict reusable representation families:
  eqType/equality, Nat arithmetic/order, truncated Nat subtraction, seq/List
  relations, seqset/List+Nodup, and half-open interval sums. The other four are
  two domain-level compositional bridges (UnitGrowth and Supremum) plus the
  Prop/SProp foundation and logical combinators. Across the 44 currently
  accepted declarations, the main Nat bridge occurs in 26 results,
  UnitGrowth in 12, Nat subtraction and Supremum in 5 each, seqset and finite
  sums in 3 each, List relations in 2, and eqType in 1. SearchArg's new
  Bool/Option layer is deliberately excluded from the formal reusable count
  until its audit/publication gate succeeds.

## 2026-09-21 13:21:42 HKT — SearchArg accepted 8 / 8

- The third and final bounded recovery route closed the proof-dependent
  `prop_on_ex_minn` declaration without unfolding the large imported
  `Nat_brecOn` / `Nat_below` implementation.  It derives the imported least
  witness laws from the actual `Nat.find` definition and its
  `Subtype.property`, relates that witness to MathComp `ex_minn` using the two
  minimality specifications, and obtains equality by imported Nat
  antisymmetry.
- All eight declarations in `util/search_arg.v` now have Rocq-compiled
  actual-artifact semantic certificates.  A fail-closed assumption audit
  reports no semantic premise, no source theorem dependency, no target theorem
  dependency, and no unexpected assumption for any declaration.  All eight
  statuses are `CERTIFIED_WITH_PROP_SPROP_FOUNDATION`; the visible logical
  boundary is `PropSPropFoundation.interpret_strict` plus the classified
  importer equality/UIP foundation.
- `SearchArgTypeAudit.v` separately kernel-checks the exact types of all seven
  imported Lean theorem constants against explicit expected types.  These
  provenance guards are not imported by the semantic certificate modules.
  The source side is automatically extracted from pinned official
  `util/search_arg.v`; its computational body is byte-exact and its theorem
  blocks/types are bound by the extraction metadata and elaborated-type
  evidence.
- The final isolated run
  `Validation/scripts/validate_utility_search_arg.sh` rebuilt the Lean module,
  exported and imported its actual artifact, compiled the source signature and
  certificates, ran Lean and Rocq assumption audits, verified the frozen
  baseline, published only after success, and passed `git diff --check`.
  The run directory is `Validation/.work/runs/utility_search_arg.gS35yF`.
- Content hashes include source `7bc98aca...e122`, Lean source
  `1536fdcd...27b9`, fresh `.olean` `ef73a70c...552f`, export
  `7fb1c0ab...26dd`, imported `.vo` `651bbb6f...8d35`, generated source `.vo`
  `5e8da148...2d5a`, statement certificate `.vo` `99ff88fa...08ba`, and exact
  target-type audit `.vo` `2544ddff...eae5`.  Full values are in the cluster
  manifest.
- Reuse accounting is now explicit.  The cross-file common library still has
  **six reusable representation-correspondence families**: eqType/equality,
  Nat arithmetic/order, truncated Nat subtraction, seq/List, seqset with
  Nodup, and half-open interval finite sums.  Together with two domain
  composition modules and two logical/foundation modules, the audited common
  library contains **ten modules**.  SearchArg successfully composes the Nat,
  Bool truth, Option, equality, and logical/witness relations across all eight
  declarations; its Bool/Option adapters remain SearchArg-local and are not
  inflated into the cross-file reusable count until another file consumes
  them or they are extracted and independently audited as common modules.
- Current batch truth is 28 translated/proof-clean and 28 accepted
  declarations: Nat 2/2, UnitGrowth 12/12, SearchArg 8/8, List 3/57, and Sum
  3/25.  Cumulative coverage is now 10 / 357 accepted files and 52 / 2439
  accepted declarations, with zero translated-but-not-certified declarations
  in the currently translated subset.

## 2026-09-21 14:55:54 HKT — List `last0` theorem cluster accepted 5 / 5

- Five additional declarations from pinned official `util/list.v` are now
  `ACCEPTED_V06_TRANSLATION`: `last0_cons`, `last0_cat`, `last0_nth`,
  `last0_ex_cat`, and `last0_filter`.  Together with the previously accepted
  `max0`, `first0`, and `last0`, List progress is **8 / 57 accepted**.  Sum
  remains **3 / 25 accepted**, so the strict accepted List+Sum total is now
  **11 declarations**.
- The fresh end-to-end command
  `Validation/scripts/validate_utility_list_last.sh` completed successfully in
  `Validation/.work/runs/utility_list_last.0NiRPl`: isolated Lean rebuild,
  exact statement-only theorem export, monomorphic computation-interface body
  export, `rocq-lean-import`, official-source extraction, Rocq certificate
  compilation, exact-target type guards, Lean/Rocq assumption audits, baseline
  audit, publication, and `git diff --check` all passed.
- All five semantic results are
  `CERTIFIED_WITH_PROP_SPROP_FOUNDATION`.  For every certificate the automatic
  audit reports `semantic_premises = []`, source theorem dependency `false`,
  target theorem dependency `false`, and `unexpected = []`.
- `last0_nth` required observable computation for actual imported `List.length`,
  truncated Nat subtraction, and `List.getD`.  Instead of importing generic
  Mathlib proof graphs, the validator exports a validation-only monomorphic
  interface of Lean-kernel-checked `rfl` equations.  Its additional audited
  importer boundary is `propext` plus the `PrimInt63` primitive type and
  operations reached by the imported `List.getD` implementation; these are
  reported explicitly and are not semantic premises.
- The certificates compositionally reuse the established Nat and ordered
  `seq`/`List` correspondences.  The new append, filter, length, `getD`, Bool
  predicate, existential-witness, and list-roundtrip lemmas are currently
  artifact-local to this List cluster.  Therefore the strict cross-file
  reusable representation-family count remains **6**, and the independently
  audited common-library module count remains **10**; local helpers are not
  inflated into either total before cross-file extraction and audit.
- Content hashes for this accepted run include official source
  `7bb5784d...a6a`, Lean source `3a542ca7...0f74`, fresh production `.olean`
  `20b14898...00a`, export `1db6417e...6b85`, imported `.vo`
  `67344f52...d721`, and generated official-source signature `.vo`
  `06621b81...5bd7`.  Full hashes and per-declaration invalidation keys are in
  `cluster_results/list_last.json`.
- Updated cumulative truth: 33 declarations in the active batch are
  translated, proof-clean, and accepted; cumulative accepted coverage is
  **10 / 357 files** and **57 / 2439 declarations**.  `util/list.v` remains a
  `PARTIAL_V06_FILE` because 49 declarations have not yet been translated;
  translated-but-not-certified debt remains zero.

## 2026-09-21 15:11:48 HKT — current-source revalidation and next List cluster

- Extending the production candidate `Prosa/Util/List.lean` invalidated the
  content hashes of the earlier List artifacts, so both existing List
  validators were rerun from fresh isolated build directories.  The starter
  cluster (`max0`, `first0`, `last0`) passed 3 / 3 and the `last0` theorem
  cluster passed 5 / 5.  The eight prior declarations are therefore again
  bound to the current production source and remain accepted; this is not a
  reuse of stale `.olean` or `.vo` files.
- Nine further pinned-v0.6 declarations have now been translated and compile
  with completed Lean proofs: `max0_cons`, `max0_of_uniform_set`,
  `in_max0_le`, `max0_in_seq`, `max0_2cons_eq`, `max0_2cons_le`, `max0_rem0`,
  `last_of_seq_le_max_of_seq`, and `max_of_dominating_seq`.  They are presently
  `PROOF_CLEAN` / `NOT_YET_VALIDATED` and are not included in accepted
  coverage.
- A temporary broad `Mathlib.Tactic` import caused the fail-closed Lean axiom
  audit to detect new `Classical.choice` and `Quot.sound` dependencies in an
  existing theorem.  The import was removed and the only affected proof was
  rewritten using explicit `Nat.succ_le_succ_iff` reasoning.  Fresh
  revalidation then passed, demonstrating that the existing acceptance state
  was not silently retained across an assumption change.
- Strict current counts are therefore **List 8 / 57 accepted** plus nine
  translated/proof-clean candidates, **Sum 3 / 25 accepted**, and **11
  accepted across List + Sum**.  The next work item is an actual-artifact
  semantic certificate for the new `max0` cluster, reusing the already audited
  Nat and ordered seq/List relations rather than switching to a new Sum
  cluster.

## 2026-09-21 15:23:43 HKT — four `max0`-family statements accepted

- `max0_cons`, `max0_2cons_eq`, `max0_2cons_le`, and
  `last_of_seq_le_max_of_seq` passed a fresh isolated end-to-end run in
  `Validation/.work/runs/utility_list_last.s2ecyP`.  The run rebuilt the
  current production module, exported the exact compiled target theorem types
  plus the actual `max0 = List.foldl Nat.max 0` body, imported them into Rocq,
  compiled the independent source/target correspondence, checked exact target
  type guards, audited assumptions, checked the frozen baseline, and published
  only after all gates succeeded.
- Each result is `CERTIFIED_WITH_PROP_SPROP_FOUNDATION`.  Automatic audit
  reports `semantic_premises = []`, source theorem dependency `false`, target
  theorem dependency `false`, and `unexpected = []`.  The certificates use
  the actual imported fold computation and do not invoke either source or
  target theorem proof constants.
- The new computation proof is compositional: the existing Nat relation,
  actual imported Nat order, and order/multiplicity-preserving seq/List map are
  reused; only an artifact-specific `foldl Nat.max` preservation lemma is
  added.  Consequently the strict cross-file reusable representation-family
  count remains **6** (and the independently audited common-module count
  remains **10**); no unreviewed local helper is counted as a new reusable
  family.
- Current strict progress is **List 12 / 57 accepted** and **Sum 3 / 25
  accepted**, hence **15 accepted across List + Sum**.  Five additional List
  declarations (`max0_of_uniform_set`, `in_max0_le`, `max0_in_seq`,
  `max0_rem0`, `max_of_dominating_seq`) are translated and Lean proof-clean
  but not yet semantically accepted.
- The generated aggregate status currently counts only declarations present in
  published semantic manifests, so it reports `translated_but_not_certified =
  0`.  For the current production source the correct operational debt is **5**;
  this discrepancy is recorded explicitly and must be corrected in the status
  generator rather than treating unmanifested production declarations as not
  translated.

## 2026-09-21 15:39:29 HKT — all nine new List statements closed

- The remaining five translated statements—`max0_of_uniform_set`,
  `in_max0_le`, `max0_in_seq`, `max0_rem0`, and
  `max_of_dominating_seq`—also passed the complete fresh actual-artifact gate.
  Together with the preceding four, all nine declarations added to the
  production candidate in this phase are now
  `CERTIFIED_WITH_PROP_SPROP_FOUNDATION` and
  `ACCEPTED_V06_TRANSLATION`.
- The key new proof component is a bidirectional relation between MathComp's
  reflected Boolean sequence membership and the exact imported Lean
  `List.Mem` inductive.  Its forward and backward directions are proved by
  structural recursion and preserve both the Nat element map and the ordered,
  multiplicity-preserving list map.  It is then composed with already audited
  length, non-emptiness, filter, `getD`, `max0`, Nat equality/order, and
  logical-quantifier correspondences.  No source or target theorem proof is
  used.
- The final isolated run is
  `Validation/.work/runs/utility_list_last.XAio4e`.  All 14 statements in the
  combined `last0`/`max0` artifact pass exact-target type guards and automatic
  assumption audits.  For every certificate:
  `semantic_premises = []`, target theorem dependency `false`, source theorem
  dependency `false`, and `unexpected = []`.
- Content hashes for the accepted run are: official source
  `7bb5784d...a6a`, current Lean source `2a8cbbb4...5c29`, fresh `.olean`
  `95e65f04...975f`, export `84b96b37...f65a`, imported `.vo`
  `ee3b45f5...ad13`, and generated source-signature `.vo`
  `688e2b64...c603`.  Full hashes and per-declaration invalidation keys are in
  `cluster_results/list_last.json`.
- Current strict progress is **List 17 / 57 accepted** and **Sum 3 / 25
  accepted**, hence **20 accepted across List + Sum**.  The active batch now
  has 42 translated, proof-clean, and accepted declarations; cumulative
  coverage is **10 / 357 accepted files** and **66 / 2439 accepted
  declarations**, with translated-but-not-certified debt back to **0**.
- Reuse accounting remains conservative: there are **6 cross-file reusable
  representation-correspondence families** and **10 independently audited
  common modules**.  The membership work is an actual-artifact instantiation
  of the existing seq/List-membership family, not a newly invented seventh
  representation.  This cluster demonstrates reuse of Nat, Nat order,
  seq/List, membership, Bool/reflection, filter, default-index, and common
  Prop/SProp combinators across nine downstream statements.

## 2026-09-21 17:01:56 HKT — `nth0_cons` accepted by bridge composition

- The source-ordered Nat/list lookup theorem `nth0_cons` was translated from
  pinned v0.6 and accepted after a fresh run in
  `Validation/.work/runs/utility_list_last.vU8Qbh`.  Its certificate composes
  the already audited cons-list relation, positive Nat order, defaulted lookup,
  truncated subtraction by one, implication, and equality correspondences.
- Status is `CERTIFIED_WITH_PROP_SPROP_FOUNDATION`; automatic audit reports no
  semantic premise, no source or target theorem dependency, and no unexpected
  assumption.  This is a direct reuse case: no new representation family was
  introduced.
- Current hashes are Lean source `a5ebf094...ea63`, fresh `.olean`
  `7bc81583...9b29`, export `9510e035...3d82`, imported `.vo`
  `1dccdac0...0098`, and generated source-signature `.vo`
  `b40edd61...e10b`.
- Strict progress is now **List 18 / 57**, **Sum 3 / 25**, and **21 accepted
  across List + Sum**.  Cumulative coverage is **10 / 357 files** and **67 /
  2439 declarations**.  All 43 declarations translated in the active utility
  batch are proof-clean and semantically accepted, so the current
  translated-but-not-certified count is zero.

## 2026-09-21 17:23:39 HKT — generic `rem` correspondence proof compiled

- Four further pinned-v0.6 List declarations are present in the production
  candidate and pass Lean compilation/proof audit: `rem_in`,
  `in_neq_impl_rem_in`, `filter_size_rem`, and `in_seq_equiv_undup`.  Adding
  them changed the production source hash, so all previously accepted 18 List
  results were rerun against the current source in fresh isolated run
  `Validation/.work/runs/utility_list_last.5oss6M`; all remained accepted.
- A new actual-artifact adapter now relates an arbitrary MathComp `eqType` and
  `seq T` to the imported Lean carrier plus its canonical `DecidableEq` and
  generic imported `List T`.  It proves two-sided list round trips, Boolean
  membership versus imported `List.Mem`, equality/disequality observation,
  and—using the kernel-checked `generic_erase_nil/cons` equations—the
  computation correspondence `rem y xs` ↔ actual imported `List.erase xs y`.
- Independent statement-correspondence proofs for `rem_in` and
  `in_neq_impl_rem_in` now compile in Rocq 9.3 against the current actual
  imported artifact.  They do not use either source theorem constant or target
  theorem constant.  Full publication, exact-target guards, and automatic
  assumption audit are still pending, so the strict accepted count remains
  **List 18 / 57**, **Sum 3 / 25**, total **21**.  These two results are
  presently `SEMANTIC_PROOF_COMPILED`, not yet `ACCEPTED`.
- This work reuses the existing eqType/DecidableEq, ordered seq/List,
  membership, Bool/reflection, and Prop/SProp components.  It is an
  artifact-specific instantiation, so the conservative reusable
  representation-family count remains **6** (10 audited common modules when
  logical and domain composition modules are included).

## 2026-09-21 17:43:03 HKT — first two generic `rem` theorems accepted

- `rem_in` and `in_neq_impl_rem_in` completed the full fresh pipeline and are
  now `CERTIFIED_WITH_PROP_SPROP_FOUNDATION` / `ACCEPTED_V06_TRANSLATION`.
  Exact target-type guards instantiate the actual imported polymorphic Lean
  theorems with the canonical `eqType`-derived `DecidableEq`; the independent
  semantic certificates do not invoke those theorem constants.
- Automatic `Print Assumptions` classification for both reports
  `semantic_premises = []`, source theorem dependency `false`, target theorem
  dependency `false`, and `unexpected = []`.  The remaining audited boundary
  is `PropSPropFoundation.interpret_strict`, plus importer equality/UIP
  foundations already on the allowlist.
- The successful source/current-artifact run is recorded under the current
  `list_last` fresh-work pointer and published in
  `cluster_results/list_last.json`; the cluster now contains 17 accepted
  theorem statements.  Strict progress is **List 20 / 57**, **Sum 3 / 25**,
  hence **23 accepted across List + Sum**.  Cumulative accepted coverage is
  **69 / 2439 declarations** and **10 / 357 files**.
- `filter_size_rem` and `in_seq_equiv_undup` remain translated and Lean
  proof-clean but not semantically accepted.  They are the only current
  unmanifested List candidates; work proceeds first through the already
  established erase/filter/length/Nat-add relations, then through the harder
  `undup`/`eraseDups` computation boundary.

## 2026-09-21 17:49:50 HKT — `filter_size_rem` accepted

- `filter_size_rem` now passes the full fresh pipeline in isolated run
  `Validation/.work/runs/utility_list_last.zmUQQG`.  The proof composes the
  already established generic `rem` correspondence with actual imported
  Boolean `List.filter` computation, generic list length, Nat addition by one,
  membership, and Nat equality.  It preserves sequence order and multiplicity;
  no `Finset` representation is introduced.
- Status is `CERTIFIED_WITH_PROP_SPROP_FOUNDATION`.  The fail-closed audit
  reports `semantic_premises = []`, source and target theorem dependencies
  both `false`, and `unexpected = []`.  The exact compiled target type is
  separately guarded with the canonical `eqType`-derived Lean `DecidableEq`.
- Strict progress is now **List 21 / 57**, **Sum 3 / 25**, hence **24 accepted
  across List + Sum**.  Cumulative coverage is **70 / 2439 declarations** and
  **10 / 357 files**.  Of the four newly translated generic List declarations,
  only `in_seq_equiv_undup` remains outside semantic acceptance.

## 2026-09-21 18:04:37 HKT — `in_seq_equiv_undup` accepted

- `in_seq_equiv_undup` completed the full fresh build/export/import/certificate
  pipeline in isolated run `Validation/.work/runs/utility_list_last.AQkMja`.
  The actual compiled Lean target type is guarded definitionally, while the
  semantic proof independently relates MathComp `undup` membership to actual
  imported Lean `List.eraseDups` membership and then transports the canonical
  membership decisions and Boolean equality.
- The imported `generic_mem_eraseDups` interface is operation-level evidence,
  not the Prosa target theorem. Its Lean proof body (`List.mem_eraseDups`) was
  checked by Lean, exported with its body, imported, and checked by Rocq. The
  correspondence certificate does not call either
  `prosa.util.list.in_seq_equiv_undup` or
  `Prosa_Util_List_in_seq_equiv_undup`.
- Automatic assumption classification reports
  `semantic_premises = []`, source theorem dependency `false`, target theorem
  dependency `false`, and `unexpected = []`. Status is
  `CERTIFIED_WITH_PROP_SPROP_FOUNDATION`; audited boundaries are
  `PropSPropFoundation.interpret_strict`, importer equality/UIP, `propext`, and
  `Quot.sound` from the imported operation proof.
- Strict progress is now **List 22 / 57**, **Sum 3 / 25**, hence **25 accepted
  across List + Sum**. Cumulative coverage is **71 / 2439 declarations** and
  **10 / 357 files**; current translated-but-not-certified debt remains zero.
  This result reuses the existing eqType/DecidableEq, ordered seq/List,
  membership, Bool/reflection, and logical-relation families, so the
  conservative cross-file representation-correspondence count remains **6**.

## 2026-09-21 18:15:20 HKT — `seq1_some` accepted by correspondence composition

- The new v0.6-only `seq1_some` translation compiles and is proof-clean. Its
  independent Rocq certificate composes the already established
  eqType/DecidableEq boundary, generic seq/List equality correspondence,
  Option constructor/equality correspondence, Boolean-decision correspondence,
  and Boolean equality correspondence. It does not reproduce the Lean proof.
- Full fresh validation succeeded in
  `Validation/.work/runs/utility_list_last.AfvxeN`. The exact imported theorem
  type is separately guarded, and the certificate audit reports
  `semantic_premises = []`, source theorem dependency `false`, target theorem
  dependency `false`, and `unexpected = []`. Its status is
  `CERTIFIED_WITH_PROP_SPROP_FOUNDATION`; the only non-importer logical boundary
  is `PropSPropFoundation.interpret_strict`.
- Strict progress is now **List 23 / 57**, **Sum 3 / 25**, and **26 accepted
  across List + Sum**. Cumulative coverage is **72 / 2439 declarations** and
  **10 / 357 files**, with translated-but-not-certified debt zero.
- The project-local `prosa-v06-translation` skill was also tightened to require
  correspondence-DAG extraction, aggressive reuse of certified lower-level
  relations, separate certification of missing operation interfaces, explicit
  reused/new/unresolved dependency reporting, and source/target theorem
  self-dependency rejection. The updated skill passes its structural validator.

## 2026-09-21 18:24:57 HKT — `seq_elim_last` accepted

- `seq_elim_last` completed the full pipeline in fresh isolated run
  `Validation/.work/runs/utility_list_last.UQOxpm`. Its certificate relates
  arbitrary source/target list and Nat inputs, maps nested existential witnesses
  in both directions, and composes certified length, append, singleton,
  equality, implication, and conjunction correspondences.
- This is deliberately not a second proof of the theorem's truth. The forward
  certificate maps any source theorem-statement witness to a target witness;
  the backward certificate maps any target witness back to a source witness.
  Neither source nor target theorem constant occurs in that construction.
- Automatic audit reports `semantic_premises = []`, source theorem dependency
  `false`, target theorem dependency `false`, and `unexpected = []`. Status is
  `CERTIFIED_WITH_PROP_SPROP_FOUNDATION`; assumptions are importer equality and
  `PropSPropFoundation.interpret_strict`.
- Strict progress is **List 24 / 57**, **Sum 3 / 25**, hence **27 accepted
  across List + Sum**. Cumulative coverage is **73 / 2439 declarations** and
  **10 / 357 files**, with no translated-but-not-certified declaration in the
  current manifest.

## 2026-09-21 18:31:42 HKT — `in_cat` accepted with reused List DAG

- `in_cat` completed the full actual-artifact pipeline in fresh run
  `Validation/.work/runs/utility_list_last.B3yazz`. The certificate reuses the
  accepted eqType/DecidableEq membership relation, seq/List relation, nested
  existential transport, append, singleton, and list equality correspondence.
- The official source associates `left ++ ([x] ++ right)`, whereas the compiled
  Lean statement associates `(left ++ [x]) ++ right`. A small independently
  checked operation-level append-associativity bridge connects these exact
  shapes; the theorem is therefore certified as a semantic reformulation rather
  than incorrectly relying on syntactic identity.
- Automatic audit reports no semantic premise, no source/target theorem
  dependency, and no unexpected assumption. Status is
  `CERTIFIED_WITH_PROP_SPROP_FOUNDATION`, with only importer equality/UIP and
  `PropSPropFoundation.interpret_strict` in the audited boundary.
- Strict progress is now **List 25 / 57**, **Sum 3 / 25**, hence **28 accepted
  across List + Sum**. Cumulative coverage is **74 / 2439 declarations**, with
  **10 / 357 files** accepted and translated-but-not-certified debt zero.

## 2026-09-21 18:47:00 HKT — coarse module invalidation efficiency audit

- The concern about repeated `List.lean` invalidation is confirmed. There are
  currently **27** `utility_list_last.*` fresh work directories; **25** reached
  a freshly imported `ImportedListLast.vo`, and **21** reached the final
  `ListLastAssumptionAudit.vo` stage. A normal recent successful end-to-end run
  takes about **64–75 seconds**; earlier runs commonly took **118–123 seconds**.
- Consequently, even the conservative one-minute-per-audit lower bound is more
  than **21 minutes** spent in repeated full-pipeline execution. The raw sum of
  directory-birth-to-final-audit spans is about **51 minutes**, but this is not
  an exact runtime total because several work directories were later reused for
  certificate-development probes. It must not be reported as 51 minutes of
  purely avoidable work.
- The integrity rule itself is correct: a changed source must not silently reuse
  stale evidence. The avoidable cost comes from the current coarse artifact
  design: accumulated targets share one production `.olean`, one export, one
  imported Rocq module, and one assumption-audit module. An append-only new
  declaration therefore changes every aggregate hash and forces old targets
  through the pipeline again even when their elaborated types, bodies, and
  semantic dependency closures are unchanged.
- A second avoidable cost is target development: to inspect a newly compiled
  theorem type, the current script runs nearly the whole validator and then
  intentionally fails publication until its certificate is added. A dedicated
  fresh `prepare-target-artifact` mode could stop after compile/export/import.
- Recommended next optimization, not implemented in this audit: translate and
  certify several declarations per semantic cluster; export target signatures
  in content-addressed per-target/per-cluster artifacts; keep stable
  computational interfaces separate; invalidate an accepted certificate only
  when its own elaborated declaration fingerprint or certified dependency
  closure changes; and run one full regression at cluster close. This preserves
  stale-artifact protection while avoiding theorem-by-theorem replay.

## 2026-09-21 19:12:59 HKT — incremental List batch selected and Lean candidates compile

- Work is restricted to `util/list.v`; Sum remains unchanged. The next frozen
  batch contains five dependency-compatible targets:
  `filter_in_pred0`, `rem_all`, `nin_rem_all`, `in_rem_all`, and `rem_lt_id`.
- Selection rationale: the batch reuses the already certified eqType /
  `DecidableEq`, ordered `seq` / `List`, membership, Boolean-predicate/filter,
  Nat-order, and Prop/SProp bridges. The one new operational dependency is the
  recursive `rem_all` computation, which is shared by the final three theorem
  statements and already has a historical actual-artifact proof pattern that
  must be rebound to the new v0.6 artifact.
- The five production candidates were translated from the pinned v0.6 source.
  `filter_in_pred0` is correctly adapted from source Boolean negation to the
  equivalent Lean equation `P x = false`; `rem_all` preserves source structural
  recursion and uses the approved `DecidableEq` boundary.
- `lake env lean Prosa/Util/List.lean` passed under Lean 4.33.1 with no
  `sorry`; only pre-existing unused-simp linter warnings were emitted. This is
  translation/proof progress only, not semantic acceptance.
- The current `List.lean` source is now the candidate snapshot to be frozen by
  the new minimal prepare/check/finalize workflow. No historical List evidence
  is counted against this changed snapshot until the final batch regression.

## 2026-09-21 19:33:52 HKT — prepared snapshot reused; five new semantic proofs close

- The new `prepare` phase sealed snapshot
  `22271524e031d9248634acd07fc816acfaa0032fe0cd9488cc67a26564b4314b`.
  Measured fresh-stage times were: Lean build `17.762879s`, official-source
  acquisition `2.025433s`, export `0.813817s`, and Rocq import `33.430008s`
  (`54.032137s` total measured preparation).
- Subsequent certificate iterations hash-verified and reused that snapshot.
  The successful check recorded four `VERIFIED_CACHE` hits for those stages;
  none of Lean build, source acquisition, export, or import executed. The final
  new-certificate compile took `3.828762s` and its assumption audit `0.032977s`.
- Rocq 9.3 compiled actual-artifact certificates for all five batch targets.
  `rem_all_recursive_certificate` is `CERTIFIED` and uses the imported
  production computation plus kernel-checked recursion equations. The four
  theorem-statement certificates (`filter_in_pred0`, `nin_rem_all`,
  `in_rem_all`, `rem_lt_id`) are
  `CERTIFIED_WITH_PROP_SPROP_FOUNDATION`.
- Every new audit reports `semantic_premises=[]`, source theorem dependency
  false, target theorem dependency false, and no unexpected assumptions.
  `rem_all` has no Prop/SProp assumption; the theorem statements expose only
  the already approved `PropSPropFoundation.interpret_strict` boundary plus
  classified importer equality/UIP foundations.
- These are successful intermediate checks, not yet published acceptance. The
  current snapshot still requires one unified regression of the prior 25 List
  declarations plus these five targets, Lean proof audit, baseline audit, and
  publication.

## 2026-09-21 19:54:52 HKT — five-target List batch accepted; incremental validator verified

### Translation and semantic result

- The frozen final List snapshot is
  `520b1687056e977a1d6089c944dee3b5fc1b976d8f3965c4af2c927640a09ec8`.
  It includes one Lean build of `Prosa/Util/List.lean`, both applicable export /
  import groups, and the exact official-source extractions used by all 30
  current List certificates.
- The batch added and accepted five declarations:

  | declaration | status | new semantic dependency |
  | --- | --- | --- |
  | `filter_in_pred0` | `CERTIFIED_WITH_PROP_SPROP_FOUNDATION` | none; composes certified equality, membership, Bool/filter, and List bridges |
  | `rem_all` | `CERTIFIED` | recursive `rem_all` operation correspondence over the actual imported body |
  | `nin_rem_all` | `CERTIFIED_WITH_PROP_SPROP_FOUNDATION` | reuses certified `rem_all` and membership |
  | `in_rem_all` | `CERTIFIED_WITH_PROP_SPROP_FOUNDATION` | reuses certified `rem_all` and membership |
  | `rem_lt_id` | `CERTIFIED_WITH_PROP_SPROP_FOUNDATION` | reuses monomorphic Nat/List `rem_all`, membership, length, and `<` correspondence |

- The final regression rechecked the prior 25 List targets and the five new
  targets together. All **30 / 30** compile, are proof-clean, pass semantic
  correspondence, and pass the fail-closed assumption audit. Across the 30,
  3 are `CERTIFIED` without the Prop/SProp axiom and 27 are
  `CERTIFIED_WITH_PROP_SPROP_FOUNDATION`. Every result has
  `semantic_premises=[]`, source theorem dependency `false`, target theorem
  dependency `false`, and `unexpected=[]`.
- One audit issue was detected rather than hidden: the compiled Lean proof of
  `rem_lt_id` uses the already approved standard foundation `Quot.sound`. Its
  initial target-specific allowlist omitted that fact, so finalize failed
  closed. The allowlist was corrected to the observed exact pair
  `[propext, Quot.sound]`; no semantic axiom or premise was added.
- The exact `lean4export` artifact format deliberately contains trailing field
  separators. A narrowly scoped Git attribute now excludes generated `.out`
  files from whitespace diagnostics while preserving their exact imported
  bytes and hashes. `git diff --check` passes.

### Prepare / check / finalize behavior

- `prepare_utility_list_batch.sh` owns source verification, Lean build,
  official-source acquisition, export, and Rocq import. Its manifest binds the
  complete production Lean tree, source/tool commits, tool binaries, module
  loading configuration, options, input hashes, output set, and each output
  hash.
- `check_utility_list_batch.sh` verifies that manifest and then rebuilds only
  the affected Rocq certificate layer and assumption audit. A certificate-only
  marker edit retained snapshot `520b...a09ec8`: all four prepare stages were
  `VERIFIED_CACHE`, with zero Lean build/export/import execution. Restoring the
  certificate and checking again gave the same result; the second check also
  reused its validated lower-level certificate base.
- `finalize_utility_list_batch.sh` runs the unified 30-target regression and
  publishes only after the full Lean axiom audit, Rocq assumption audit,
  baseline audit, and provenance checks succeed. Publication records
  `CURRENT_SNAPSHOT` plus per-stage `FRESH` / `VERIFIED_CACHE`; it no longer
  hard-codes `fresh_build=true`.

### Invalidation and corruption tests

- **Same inputs:** repeated prepare calls on the final snapshot produced four
  verified cache hits and executed no target stage.
- **Certificate-only change:** prepare verification took `0.001758s`; only
  certificate compilation (`3.856587s`) and audit (`0.033226s`) ran. Lean
  build, source acquisition, export, and import did not run.
- **Related Lean input change:** a temporary validation-only computation-
  interface marker changed the snapshot to `f96bbdcb...` and forced all four
  stages to execute: Lean build `17.933845s`, source acquisition `3.303088s`,
  export `2.636761s`, and Rocq import `33.969777s`. Removing the marker restored
  the original snapshot, which was hash-verified from cache.
- **Corrupted artifact:** a copied prepared source artifact was altered. Cache
  verification exited nonzero with
  `PREPARED_ARTIFACT_HASH_MISMATCH:source_acquisition:source/GeneratedListLastSource.v`
  and emitted no success evidence.
- **Incremental versus clean:** the incremental finalize used verified prepare
  artifacts and took `22.754466s` across all recorded phases. A subsequent
  `CLEAN_FULL` run executed all seven phases: Lean build `17.305738s`, source
  acquisition `3.538602s`, export `1.952283s`, Rocq import `34.289977s`,
  certificate compilation `13.494349s`, audit `6.836643s`, and publication
  `0.511772s` (`77.929364s` total). The comparison reports the same snapshot,
  identical 30 declaration acceptance results, and identical semantic /
  assumption boundaries.

### Instrumented execution counts

The machine summary covers all 19 instrumented prepare invocations during
development, recovery, invalidation testing, and clean reproduction. There
were four actual executions of each prepare stage (the provisional snapshot,
the final expanded snapshot, the intentional Lean-input mutation, and the
required clean reproduction) and 15 verified-cache uses of each stage, i.e.
60 validated stage-level cache hits. Recorded totals are:

| stage | executions | verified cache hits | measured seconds |
| --- | ---: | ---: | ---: |
| Lean build | 4 | 15 | 71.329487 |
| source acquisition | 4 | 15 | 12.076003 |
| export | 4 | 15 | 7.432120 |
| Rocq import | 4 | 15 | 135.726467 |
| certificate compile | 7 | 0 | 65.502614 |
| audit | 6 | 0 | 25.792372 |
| publication | 3 | 0 | 1.544008 |

Failed runs are fail-closed and are counted only for stages that emitted a
completed timing event; no elapsed time is inferred from report timestamps.
Machine evidence is under
`Validation/logs/utility_foundation_expansion/list_batch/`, notably
`incremental_tests/timing_execution_summary.json` and
`incremental_tests/clean_full_equivalence.json`.

### Current coverage after publication

- List: **5 newly accepted**, **30 / 57 cumulative accepted**, **27 remaining**.
- Sum: unchanged at **3 / 25**.
- Project: **79 / 2439 accepted declarations**, **10 / 357 accepted whole
  files**, and **0 translated-but-not-certified declarations** in the current
  manifest.
