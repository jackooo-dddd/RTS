# Classic validation: recorded tool changes

## 2026-10-02 — lean4export: filtered `Finset.Ico` sums in the theorem-type projector

- **Why.** Classic statements write MathComp's `\sum_(m <= i < n | P i) F i` as
  `∑ i ∈ (Finset.Ico m n).filter (fun i => P i = true), F i` (`classic/util/sum.v`,
  `classic/analysis/global/basic/interference_bound_edf.v`).  Exported unprojected, such a type drags
  `Nat.instLocallyFiniteOrder` (omega-built `Nat.Internal.Linear` proofs) into the export and the Rocq
  import does not finish (observed: >30 min, killed).  The existing projector
  (`projectNatIcoSum?`, `normalization.subexpression_heads = ["Finset.sum"]`) handled only the unfiltered form.
- **Change.** `projectNatIcoSum?` also accepts `Finset.filter p dec (Finset.Ico m n)` and projects it to
  `List.foldr Nat.add 0 (List.map f (List.filter (fun i => @decide (p i) (dec i)) (List.range' m (n - m) 1)))`
  (loose bound variables of `p`/`dec` lifted under the new binder).  The unfiltered branch is byte-for-byte the
  previous behaviour.  Patch: `tooling/classic/lean4export_filtered_ico_sum.patch`.
- **Soundness.** Unchanged mechanism: every normalized theorem type is guarded in the export-root fixture by a
  theorem `original = projected` proved by `Eq.refl` and checked by the Lean kernel before export
  (`kernel_guard_artifacts`, same projector code in the fixture).  A first version that did not lift loose
  bound variables was rejected by these guards (`normalization is not definitionally equal: leq_sum_nat`).
- **Binary pin.** `scripts/common/validation_common.sh` previously pinned
  `c20dbe1f14951dbcb2b806395f171d3e91e9bb5ccc22fa5cb63bd592a767e49b`; that binary is reproduced bit-for-bit
  by rebuilding the pre-change source with Lean 4.33.1 (verified 2026-10-02).  New pin:
  `a09f6140cb75c5f67f1fd0a19e7b18c006fbae33644b55015e668215e8af99ed` (source `Export.lean` sha256
  `4b676505b29022249918653e4c52cfdda9c7aae9bee031bc9c778ebfeb6c61b1`).  Exports without filtered `Finset.Ico`
  sums are unaffected; accepted v0.6 publications keep their recorded exporter hashes.
- **Manifest.** `tooling/tooling_manifest.json` `lean4export`: `expected_binary_sha256`, `patch_sha256` and
  `expected_diff_sha256` updated (the full exporter diff against upstream `c9f8373` is
  `tooling/patches/lean4export.patch`); the previous values and the previous patch
  (`tooling/patches/lean4export.c20dbe1f.patch`) are kept under `lean4export.history`.

## 2026-10-02 — lean4export: opt-in reducible `Nat` aliases as `Finset.Ico` sum index types

- **Why.** Classic schedule statements sum over `Finset.Ico t1 t2` with `t1 t2 : time`
  (`Prosa.Classic.Model.Time.Time.time`, a reducible `abbrev` of `Nat`), so the elaborated index type of
  `Finset.sum`/`Finset.Ico` is `time`, not syntactically `Nat`.  `projectNatIcoSum?` matched only `Nat`, so
  such sums were exported unprojected, dragging `Nat.instLocallyFiniteOrder` (its `Nat.Internal.Linear`
  proofs) into the export; the Rocq import stalled at `Nat.Internal.Linear.ExprCnstr.denote_toNormPoly`
  (observed for `classic/model/schedule/global/basic/schedule.v`, killed after >3 min without progress).
  The kernel guard did not catch it because an unprojected type is trivially equal to itself.
- **Change.** The index-type test of `projectNatIcoSum?` (the summation index of `Finset.sum` and the carrier of
  `Finset.Ico`) accepts, besides `Nat`, the constants listed (one fully qualified name per line) in the new
  environment variable `LEAN4EXPORT_NAT_INDEX_ALIASES`.  The variable is empty unless a spec sets it through
  `export_env`, so every export without it is byte-for-byte the previous behaviour; the projected form is the
  same `List.foldr Nat.add 0 (List.map f (List.range' m (n - m) 1))`.  Patch:
  `tooling/classic/lean4export_nat_index_aliases.patch`.
- **Pipeline.** `translation_file_pipeline.py` allows the key `LEAN4EXPORT_NAT_INDEX_ALIASES` in a spec's
  `export_env` (next to `LEAN4EXPORT_PRESERVE_REDUCIBLE_THEOREM_TYPES`).  Backup of the previous pipeline:
  session scratchpad `translation_file_pipeline.pre_aliasenv.py`.
- **Soundness.** Unchanged mechanism: the exporter still checks `Meta.isDefEq original projected` for every
  normalized theorem type, and the export-root fixture still proves `original = projected` by `Eq.refl` checked
  by the Lean kernel (its projector copy accepts exactly the same alias, `time`).  A first build gated the
  codomain argument of `Finset.sum` instead of the index argument; its guard was again the identity (no
  projection), which was caught by printing the guard before export, and the binary was rebuilt.
- **Binary pin.** Previous pin `a09f6140cb75c5f67f1fd0a19e7b18c006fbae33644b55015e668215e8af99ed` is reproduced
  bit-for-bit by rebuilding the pre-change source (verified 2026-10-02).  New pin
  `ffdad67b221c7b4a8b08f7ac0460002586d9587662bd3b907bda301bcffd1e00`; `tooling/tooling_manifest.json`
  `lean4export` updated with a `history` entry (previous full patch kept as
  `tooling/patches/lean4export.a09f6140.patch`).
- **Pre-flight.** Each classic export closure is now probed before the Rocq import for constants under
  `Nat.Internal.Linear`/`Int.Internal.Linear`/`Nat.Linear`/`Int.Linear` (session tool `export_closure_probe.py`);
  fixture proofs avoid lemmas whose proof closure contains them (e.g. `List.sublist_mergeSort`,
  `Finset.sum_filter`), using structural proofs instead.

## 2026-10-02 — pipeline: classic module-qualified display names in the source fingerprint comparison

- **Why.** Classic declaration names carry their Rocq module path (`ResponseTime.is_response_time_bound_of_task`).
  The official evidence context loads every classic file, including the uniprocessor `response_time.v` that
  declares a module of the same name, so the official `Check` prints this file's declarations as
  `@global.response_time.ResponseTime.x` (head and, for own definitions, inside types), while the validation
  context prints `@ResponseTime.x`.  The existing own-module-qualifier rule assumed the declaration name is the
  last path component, so it did not cover a module-qualified declaration name.
- **Change** (`translation_file_pipeline.py`, `fingerprint_matches`, classic family only): (1) accept exactly a
  trailing suffix of the file's own logical path (`global.response_time`, `response_time`, ...) in front of exactly
  this declaration's own name at the head; (2) for the opt-in `own_qualified_in_type` names that carry a module
  path, accept exactly those file-path qualifiers inside the type, together with (1).  Result label unchanged
  (`EXACT_MODULO_OWN_MODULE_QUALIFIER`).  v0.6 behaviour unchanged (the new branches require family `classic` and a
  dotted declaration name).  Backup: session scratchpad `translation_file_pipeline.pre_modqual.py`.

## 2026-10-02 — pipeline: classic module-qualified dependency names in the source fingerprint comparison

- **Why.** `classic/model/schedule/global/basic/constrained_deadlines.v` (rank 42) states hypotheses with the global
  `Platform.work_conserving` and `Platform.respects_FP_policy`.  The official evidence context also loads
  `apa/platform.v`, which declares a module `Platform` too, so the official `Check` prints those dependencies as
  `global.basic.platform.Platform.work_conserving` inside the type, while the validation context (whose closure
  has only the global `platform.v`) prints `Platform.work_conserving`.  The existing opt-in
  `dependency_qualified_in_type` rule (v0.6) strips the qualifier down to the last name component, which does not
  fit classic names that carry their Rocq module path (and its uniqueness check, by last component, cannot pass).
- **Change** (`translation_file_pipeline.py`, `fingerprint_matches`, classic family only): for the opt-in
  `dependency_qualified_in_type` declarations (fully qualified, each required to be a declaration of a closure file
  other than this one, with its module-path name unique among the closure's declarations), accept exactly the
  trailing suffixes of that declaration's file logical path in front of exactly its module-path name inside the
  type, together with exactly the own-module qualifiers already accepted (head; `own_qualified_in_type` names).
  Label `EXACT_MODULO_DEPENDENCY_AND_OWN_MODULE_QUALIFIER` (an existing v0.6 label).  The v0.6 branch is unchanged
  and now runs only for v0.6 specs.  Used by rank 42 for exactly the two names above.  Backup: session scratchpad
  `translation_file_pipeline.pre_depqual.py`.

## 2026-10-02 — lean4export: opt-in reducible `Nat` aliases also as `Finset.Ico` sum codomains

- **Why.** `classic/analysis/global/basic/interference_bound_edf.v` (rank 48) states
  `interference_bound_edf_simpl_by_concatenation_of_intervals` as an equation between `\sum_(a <= t < b) 1 + ...`
  and a `time`-valued expression, so Lean elaborates those `Finset.Ico` sums with codomain `time` (the reducible
  alias of `Nat`), not syntactically `Nat`.  `projectNatIcoSum?` required the codomain to be `Nat`, left the sums
  unprojected, and the pre-flight guard check reported `UNPROJECTED #[Finset.sum, Finset.Ico]` (the export was
  not started, so no import hang occurred).
- **Change** (`Export.lean`, `projectNatIcoSum?`): the codomain test uses the same `natIndexType` as the index
  test, i.e. `Nat` or a constant listed in `LEAN4EXPORT_NAT_INDEX_ALIASES` (opt-in, empty by default: exports
  without the variable are unchanged).  The projected form is unchanged (`List.foldr Nat.add 0 (List.map f
  (List.range' m (n - m) 1))`).  Patch: `tooling/classic/lean4export_nat_codomain_aliases.patch`.  The export-root
  fixture's kernel-guard projector copy (generated, rank 48) makes exactly the same one-line change.
- **Soundness.** Unchanged mechanism: every normalized theorem type is checked `Meta.isDefEq` against the original
  by the exporter, and the fixture proves `original = projected` by `Eq.refl`, checked by the Lean kernel.
- **Binary pin.** Built with the recorded toolchain (`ELAN_TOOLCHAIN=leanprover/lean4:v4.33.1 lake build`); the
  previous source rebuilds bit-for-bit to the previous pin `ffdad67b221c7b4a8b08f7ac0460002586d9587662bd3b907bda301bcffd1e00`
  (verified 2026-10-02).  New pin `010c28dc3233dc40fe2a732076d2a4c233dbeaffaaf3f8978bb1b342a36d8f46`
  (`scripts/common/validation_common.sh`, `tooling/tooling_manifest.json` with a `history` entry; previous full
  patch kept as `tooling/patches/lean4export.ffdad67b.patch`).  Exports of accepted files are not re-run.
- **Regression check (2026-10-02).** The already accepted rank 36 (`classic/analysis/global/basic/workload_bound.v`,
  which uses `LEAN4EXPORT_NAT_INDEX_ALIASES` and statement normalization) was re-exported from scratch with the new
  binary: the export is byte-identical to the accepted one (`export_sha256`
  `e0a13f244c68b21df6200a652b8a774b79ad306a0939210f8695467f43c8710d`, as in its module manifest).  The fresh run is
  kept as `.work/experiments/classic_analysis_global_basic_workload_bound_regress_toolchange3`.

## 2026-10-03 — comprehensive classic validation: full-scope planning inputs (opt-in)

- **Why.** The user asked to validate the whole classic folder (`classic-prosa/comprehensive-classic`, 190 files),
  but `planning/classic_dependency` (authoritative inventory/evidence) covers only the 49 case-study files.
- **New script** `scripts/classic_full_reference_evidence.py` (the case-study script and its outputs are unchanged):
  fresh hash-checked build of the 190 classic files + the 16 util files they require in the opam switch `prosa-0.6`
  (`.work/classic_full_reference_rocq90`), and `planning/classic_full_dependency/` (file inventory, DAG, Print-Module
  declaration inventory for all 190 files, `Check @name` evidence, scope/prelude).  Evidence display context = the
  run fingerprint probe header of `classic_mkfile.py` (the declaration's file closure `Require Import`ed
  alphabetically, then MathComp's notation modules); `generation_summary.json` records how many of the 525
  case-study evidence texts are identical in this context.
- **Pipeline** (`translation_file_pipeline.py`, additive): spec field `classic_scope: "full"` (classic family only)
  switches the planning directory to `planning/classic_full_dependency` (inventory, evidence, DAG, coverage
  denominators 190/N); the manifest then records `classic_scope` with the evidence/inventory hashes.  Specs without
  the field behave byte-identically.  `classic_mkfile.py`: config `classic_scope: "full"` reads the same planning
  directory and writes the spec field.  Backups: session scratchpad `translation_file_pipeline.pre_fullscope.py`
  (sha e87e24a9…), `classic_mkfile.pre_fullscope.py`.
- **Declaration enumeration (full scope, 2026-10-03).** The first full evidence run showed two defects of the
  case-study source scanner (which never mattered for the 49 case-study files): a module alias
  (`Module X := M.`) was treated as opening a block, so every later name got a wrong prefix and was dropped; a
  `Section` named like its enclosing `Module` (`model/schedule/uni/limited/platform/limited.v`) closed the module.
  `classic_full_reference_evidence.py` now has its own scanner (one stack for sections and modules; aliases and
  signature-ascribed modules do not open blocks) and its `Print Module` parser also lists `Record` entries.
  Regression: on all 49 case-study files the new scanner yields exactly the old name lists.  The case-study
  script and its outputs are unchanged.  Inventory policy (as for v0.6 and the case study): source-level
  commands are declarations; record projections, `HB.instance`-generated constants, `Program` obligations and
  auto-generated schemes are covered through their parent declaration's certificate and are recorded in
  `generation_summary.json` as `generated_dropped`.

## 2026-10-03 — publish gate: `fun=>` body-lambda parentheses on the `Check @name` path (display only)

- **Why.** Ranks 168/169 (`classic/model/schedule/uni/limited/{edf,fixed_priority}/response_time_bound.v`) compile all
  certificates and pass `check`, but `publish` rejected `instantiated_task_interference_is_bounded` with
  "source type mismatch".  The only difference between the official evidence (Rocq 9.0) and the validation
  toolchain (Rocq 9.3) is the already-accepted display difference `TYPE_EQUAL_MODULO_SSR_FUN_WILDCARD_BODY_PARENS`
  (9.0: `fun=> (fun A R : T => e)`, 9.3: `fun=> fun A R : T => e`).  That rule was implemented only for extracted
  statement bodies (`statement_X = ... : Prop`), not for the `Check @name` output these declarations are compared
  through, and it did not cover a body lambda that is itself a wildcard lambda (`fun=> (fun=> (fun R : T => e))`,
  rank 169).
- **Change** (`translation_file_pipeline.py`): one helper `ssr_fun_body_unparen` removes exactly the parentheses
  around a `fun=>` body that starts with `fun ` or `fun=>` (balanced-paren scan, nothing else); it is used by the
  existing statement-body rule (unchanged behaviour for non-nested cases) and by a new `Check`-path rule that
  accepts `got == ssr_fun_body_unparen(normalized_check)` (also with the own-module display qualifier, as the
  neighbouring MathComp-int rule).  The recorded category is the existing
  `TYPE_EQUAL_MODULO_SSR_FUN_WILDCARD_BODY_PARENS`.  No other difference is accepted.
  Backup: session scratchpad `x/translation_file_pipeline.pre_ssrfun_check.py` (sha256 prefix c34ef9b8e22dbe95).

## 2026-10-03 — user decisions for the last comprehensive-classic blockers

The user approved (2026-10-03) three narrowly scoped mechanisms for the files that could not be accepted otherwise.

### (1) Proof-only patch of the module under validation (opt-in, rank 172)
- **Why.** The official `classic/analysis/global/jitter/bertogna_edf_theory.v` does not compile under the validation
  toolchain (Rocq 9.3 + MathComp 2.6): the rewrite chain at line 332 no longer reaches the `ltn_add2r` redex.
  The file-local `Set SsrOldRewriteGoalsOrder.` flag (the only module change allowed so far) does not fix it.
- **Change** (`translation_file_pipeline.py`, additive): spec field `official_closure.module_change = "proof_only_patch"`
  allows a recorded closure patch to touch the module itself; `module_proof_only(official, compiled)` requires that,
  with every proof interior (lines between a `Proof.` line and its `Qed.`/`Defined.`) blanked, the two files are
  identical, and that no changed line contains `Admitted`, `admit`, `Abort` or an axiom/parameter/hypothesis command.
  The statement types are still checked against the official Rocq 9.0 evidence.  The manifest records
  "recorded proof-only patch".  `classic_mkfile.py` passes the config field through; specs without it are unchanged.
- **Patch.** `patches/classic/rocq93-analysis-global-jitter-bertogna_edf_theory.patch` (the one-line fix
  `by rewrite !ltn_add2r.` from `classic-prosa/rocq93-port/prosabuddy-classic-rocq93.patch`), mapped to its file in
  `patches/classic/util_patch_map.json`, so every closure containing the file (172, 182, example 190) applies it;
  only 172 (the module itself) needs `module_change`.
- Tested: the real patch passes; a statement change and an `admit` are both rejected.
  Backups: session scratchpad `x/translation_file_pipeline.pre_proofonly.py`, `x/classic_mkfile.pre_proofonly.py`.

### (2) Goal-only validation of the 12 classic example files (new script)
- **Why.** The example files state closed results about concrete task sets built from section-local `Let`s of
  concrete records; the Lean translations use concrete Lean structures; there are no inputs to relate.
- **New script** `scripts/validate_goal_only_classic.py RANK [--publish]` (the v0.6 goal-only validator is unchanged):
  restricted to `classic/implementation/**/*_example.v`; checks the pinned source, accepted dependencies, compiles the
  byte-identical module on its verified official closure (recorded patches only on other closure files, the classic
  compatibility prelude), requires a Lean declaration for every inventory declaration, forbids Lean escapes
  (`sorry`, `admit`, `axiom`, `unsafe`, `native_decide`, `implemented_by`, `extern`), checks every imported accepted
  translation against its manifest's `production_source_sha256`, builds the module and audits axioms (standard Lean
  axioms only).  Publication: `ACCEPTED_CLASSIC_FILE` with `acceptance_mode` GOAL_ONLY, `certified: 0`; the file is
  added to `accepted_files`, its declarations to `goal_only_declarations` (tallied from the goal-only manifests),
  never to `accepted_declarations` (certified declarations only).  `file_order.csv` notes "goal-only mode".

### (3) Functional extensionality for ranks 86 and 166 only
- **Why.** `sustainability.v` (86) and `allcosts/main_claim.v` (166) state equalities of parameter functions and of
  job-parameter records holding functions; relating Rocq `=` with Lean `Eq` on functions needs functional
  extensionality, which Lean proves (quotients) but Rocq only has as the axiom
  `FunctionalExtensionality.functional_extensionality_dep`.
- **Scope.** Admitted only in the assumption audits of these two files (to be implemented as an explicit opt-in
  category, never a blanket allowlist).
- **Implementation (2026-10-04).** (a) `audit_assumptions.py`: new config key `rocq_functional_extensionality`
  (default empty); an assumption listed there is reported in its own category, and a certificate whose only
  non-foundation assumption is that axiom gets status `CERTIFIED_WITH_FUNCTIONAL_EXTENSIONALITY` (or
  `CERTIFIED_WITH_PROP_SPROP_FOUNDATION_AND_FUNCTIONAL_EXTENSIONALITY`); any other assumption still fails.
  (b) `translation_file_pipeline.py`: constant `FUNEXT_FILES` = the two sources above; at publish the funext
  category is accepted only if the family is `classic`, the spec sets `rocq_funext_scope: true`, the source is in
  `FUNEXT_FILES`, and the reported names are a subset of `{FunctionalExtensionality.functional_extensionality_dep}`;
  the per-certificate status is recorded in `assumption_summary.json`. (c) `classic_mkfile.py` forwards the config
  key and sets the spec flag. Backups: scratchpad `x/audit_assumptions.pre_funext.py`, `x/translation_file_pipeline.pre_funext.py`.
- **Result.** Rank 86 ACCEPTED 2026-10-04; certificates that do not use the axiom keep their ordinary status
  (e.g. `corresponding_labels`: `CERTIFIED_WITH_PROP_SPROP_FOUNDATION`, `default_val`: `CERTIFIED_WITH_FUNCTIONAL_EXTENSIONALITY`).
- **Rank 166 (2026-10-04).** ACCEPTED; the statement certificate
  `SustainabilityAllCostsProperty_policy_is_weakly_sustainable_correspondence` has status
  `CERTIFIED_WITH_PROP_SPROP_FOUNDATION_AND_FUNCTIONAL_EXTENSIONALITY` (only `functional_extensionality_dep`, no
  unexpected assumptions). With it all 190 comprehensive-classic files are ACCEPTED.
