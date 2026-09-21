# FOUNDATION_SLICE_2_CLOSURE Report

Report started: **2026-09-20 22:40:53 HKT**.

This report is cumulative. A Lean compilation result is not a semantic
certificate, and an unfinished correspondence is never reported as a semantic
failure without a machine-checked counterexample.

## 2026-09-20 22:40:53 HKT — Baseline frozen

- Authoritative Prosa: commit `414e66760333eaa4ef78c685bcf53291c527a548`, workspace-local clean checkout.
- Target: Lean 4.33.1 and Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`.
- Closure scope: exactly the 17 `TRANSLATED_NOT_CERTIFIED` declarations from FOUNDATION_SLICE_2; no new source file is selected.
- Accepted baseline frozen: `duration`, `instant`, `constant`, `modusponens`, `monotone`, `choose_superior`, and `supremum`.
- Their recorded type/body/invalidation hashes were read from the Slice 1 and Slice 2 manifests. The closure validator will compare them before publishing any new result.
- Starting debt: 17 declarations; 0 newly certified at this timestamp.

Planned dependency order: audited common representation bridges, then `neqP`,
`rel`, `seqset`, `subadditivity`, and the five `supremum` theorem statements.

## 2026-09-20 22:52:16 HKT — `rel.v` closure proof compiled

- Added reusable ordered `seq` ↔ imported `List` conversion and roundtrip.
- Added bidirectional membership correspondence without erasing order or multiplicity.
- Added pointwise MathComp `bool` ↔ imported Lean `Bool` truth correspondence.
- `total_over_list_correspondence_certificate`: Rocq 9.3 compile PASS.
- `antisymmetric_over_list_correspondence_certificate`: Rocq 9.3 compile PASS.
- Both certificates directly reference the actual imported definition bodies.
- Preliminary assumptions contain the approved `interpret_strict` boundary,
  imported equality definitional UIP, and the locally defined proof-irrelevant
  truth witness. No target theorem constant or semantic premise is used.

These remain preliminary until the final fresh export/import run and automatic
assumption classifier complete.

## 2026-09-20 23:05:31 HKT — `neqP` and `seqset.v` closure proofs compiled

- `neqP_statement_correspondence_certificate`: PASS in Rocq 9.3.
  It uses a canonical `eqType → Type + DecidableEq` map and separately proves
  equality and disequality observation preservation. Exact source/imported
  theorem types are bound by kernel guards, while the correspondence proof has
  no theorem self dependency. Preliminary assumptions do not include
  `interpret_strict`.
- `seqset_set_correspondence_certificate`: PASS.
- `seqset_set_of_correspondence_certificate`: PASS.
- `seqset_set_uniq_statement_correspondence_certificate`: PASS.
- The seqset bridge supplies source→target and target→source maps, observable
  list roundtrips, and a `uniq ↔ List.Nodup` correspondence. It preserves list
  order and multiplicity and does not replace the representation with a
  `Finset`.
- The seqset results expose the approved `interpret_strict` foundation,
  imported equality UIP, and a local proof-irrelevant truth witness. They will
  therefore be classified as `CERTIFIED_WITH_PROP_SPROP_FOUNDATION` if the
  final automatic audit confirms this preliminary output.

## 2026-09-20 23:21:10 HKT — all six `subadditivity.v` certificates compiled

- Inspected the actual imported artifact. Its arithmetic expressions reduce
  through the imported typeclass wrappers to the compiled Lean definitions
  `Lean.Nat_add`, `Lean.Nat_mul`, `Lean.Nat_le`, and
  `Nat_lt n m := Lean.Nat_le (Nat.succ n) m`.
- Added a reusable, kernel-checked Nat bridge with two-sided conversion,
  roundtrips, function correspondence, addition, multiplication, equality,
  `<=`, and `<` preservation. Addition and multiplication are proved from the
  imported recursive bodies; neither is assumed.
- Preliminary Rocq 9.3 compilation passed for:
  - `subadditive_at_correspondence_certificate`
  - `subadditive_until_correspondence_certificate`
  - `subadditive_correspondence_certificate`
  - `subadditive_standard_correspondence_certificate`
  - `subadditive_standard_equivalence_statement_certificate`
  - `subadditive_leq_mul_statement_certificate`
- The two theorem certificates use separate exact-type guards for source and
  target provenance. Their correspondence proofs do not use either official
  theorem proof constant.
- Preliminary `Print Assumptions` output contains only the approved
  `interpret_strict` Prop/SProp boundary plus imported equality/local singleton
  definitional-UIP markers. No semantic premise appears.
- One concrete proof issue was resolved rather than assumed: MathComp's
  `mulnS` exposes `a + a*b`, while compiled Lean `Nat.mul` recurses to
  `a*b + a`; the bridge uses the proved MathComp `addnC` rewrite and imported
  recursive addition preservation.

At this checkpoint, 17/22 declarations have either final acceptance (5) or a
preliminary Rocq-compiled semantic certificate (12). The five remaining
targets are the `supremum.v` theorem statements. No production Lean file has
been changed.

## 2026-09-20 23:34:02 HKT — all five `supremum.v` theorem certificates compiled

- Added reusable correspondence for imported Lean `List` membership,
  source `seq` membership, `Option` equality/disequality, `List` equality,
  Bool truth, Bool disjunction, and the `eqType -> Type + DecidableEq`
  boundary used by the actual theorem types.
- Reused the already certified actual-artifact relations for
  `choose_superior` and `supremum`; those definitions were not reimplemented
  as a validation-side model.
- Preliminary Rocq 9.3 compilation passed for:
  - `supremum_unfold_statement_correspondence_certificate`
  - `supremum_exists_statement_correspondence_certificate`
  - `supremum_none_statement_correspondence_certificate`
  - `supremum_in_statement_correspondence_certificate`
  - `supremum_spec_statement_correspondence_certificate`
- Each source and target theorem has a separate exact-type guard. None of the
  five semantic correspondence certificates invokes the source theorem proof
  or imported target theorem constant.
- A source/target binder-order difference was found and handled explicitly:
  MathComp's elaborated `transitive` quantifies `(y, x, z)` while the Lean
  theorem quantifies `(x, y, z)`. The semantic relation permutes the universal
  binders and preserves the premises `R x y`, `R y z`, and conclusion
  `R x z`; no theorem statement was weakened.
- Preliminary assumptions expose only the approved `interpret_strict`
  Prop/SProp foundation and importer/local singleton definitional-UIP markers.
  No semantic premise or theorem self-dependency is present in the proof
  terms seen at this stage.

All 22 Slice-2 declarations now have either the previous final acceptance
(5) or a preliminary Rocq-compiled semantic certificate (17). Publication as
22/22 accepted still requires one clean fresh Lean compile/export/import run,
fail-closed per-certificate assumption classification, baseline hash checks,
source-compatibility checks, and artifact provenance publication.

## 2026-09-20 23:45:31 HKT — first full fresh run reached the fail-closed assumption gate

- A fresh isolated run completed Lean compilation, actual-artifact export,
  Rocq import, and compilation of every common bridge and all 17 target
  certificates.
- The automatic assumption audit then correctly stopped publication. Seven
  supremum-related audit entries reported exactly one unexpected name:
  `SupremumCertificate.SupValidationTrue`.
- This is the module-qualified form of the already reviewed local SProp
  singleton definitional-UIP marker `SupValidationTrue`; it is not a new
  semantic premise or axiom. The initial allowlist contained only the short
  name because preliminary per-file compilation printed that form.
- Inspection of the machine-readable audit found no other unexpected
  assumption, no target-theorem self dependency, and no source-theorem proof
  dependency.
- The allowlist was corrected by adding that one exact fully qualified name.
  Unknown assumptions remain rejected, and no prefix-based trust rule was
  introduced.
- Because the run stopped before publication, no result from this failed audit
  is counted as accepted. The complete pipeline will be rerun from a new fresh
  build/export/import directory.

## 2026-09-20 23:46:55 HKT — exact-name issue closed; classifier edge case found

- A second fresh build/export/import and all certificate compilations passed.
- The seven previously rejected supremum audit entries now have empty
  `unexpected`, empty `semantic_premises`, and false source/target theorem
  dependency flags.
- The classifier nevertheless stopped on `common_sup_or`. Its assumption
  section contained only the explicitly allowlisted
  `SupremumCertificate.SupValidationTrue` definitional-UIP marker. The
  classifier handled `closed`, importer-only, and foundation-bearing sections,
  but omitted the valid case whose only entry is an audited local SProp
  definitional-UIP marker.
- The generic classification condition was corrected so an otherwise-clean
  section containing only exact-allowlisted definitional-UIP markers is
  `CERTIFIED`. Missing/truncated sections, semantic premises, theorem
  dependencies, and unknown assumptions remain fail-closed.
- Again, the pipeline stopped before source-compatibility checks and
  publication, so this run contributes no accepted result. A complete fresh
  run is required after the classifier fix.

## 2026-09-20 23:50:04 HKT — full fresh closure run PASS; 17/17 accepted

The third complete run used a new isolated directory:

`Validation/.work/runs/foundation_slice_2.7CedHL`

It completed the complete acceptance path: pinned-source verification, fresh
Lean compilation, actual compiled-artifact export, Rocq import, common-bridge
compilation, all 17 target certificates, marked `Print Assumptions`, automatic
fail-closed classification, source-compatibility audit, frozen-baseline audit,
content-addressed manifest generation, and publication.

### Closure result matrix

| Source declaration | Certificate status | Semantic premise | Unexpected assumption | Target/source theorem dependency | Acceptance |
| --- | --- | --- | --- | --- | --- |
| `neqP` | `CERTIFIED` | none | none | false / false | `ACCEPTED_V06_TRANSLATION` |
| `total_over_list` | `CERTIFIED_WITH_PROP_SPROP_FOUNDATION` | none | none | false / false | `ACCEPTED_V06_TRANSLATION` |
| `antisymmetric_over_list` | `CERTIFIED_WITH_PROP_SPROP_FOUNDATION` | none | none | false / false | `ACCEPTED_V06_TRANSLATION` |
| `set` | `CERTIFIED_WITH_PROP_SPROP_FOUNDATION` | none | none | false / false | `ACCEPTED_V06_TRANSLATION` |
| `set_of` | `CERTIFIED_WITH_PROP_SPROP_FOUNDATION` | none | none | false / false | `ACCEPTED_V06_TRANSLATION` |
| `set_uniq` | `CERTIFIED_WITH_PROP_SPROP_FOUNDATION` | none | none | false / false | `ACCEPTED_V06_TRANSLATION` |
| `subadditive_at` | `CERTIFIED_WITH_PROP_SPROP_FOUNDATION` | none | none | false / false | `ACCEPTED_V06_TRANSLATION` |
| `subadditive_until` | `CERTIFIED_WITH_PROP_SPROP_FOUNDATION` | none | none | false / false | `ACCEPTED_V06_TRANSLATION` |
| `subadditive` | `CERTIFIED_WITH_PROP_SPROP_FOUNDATION` | none | none | false / false | `ACCEPTED_V06_TRANSLATION` |
| `subadditive_standard` | `CERTIFIED_WITH_PROP_SPROP_FOUNDATION` | none | none | false / false | `ACCEPTED_V06_TRANSLATION` |
| `subadditive_standard_equivalence` | `CERTIFIED_WITH_PROP_SPROP_FOUNDATION` | none | none | false / false | `ACCEPTED_V06_TRANSLATION` |
| `subadditive_leq_mul` | `CERTIFIED_WITH_PROP_SPROP_FOUNDATION` | none | none | false / false | `ACCEPTED_V06_TRANSLATION` |
| `supremum_unfold` | `CERTIFIED_WITH_PROP_SPROP_FOUNDATION` | none | none | false / false | `ACCEPTED_V06_TRANSLATION` |
| `supremum_exists` | `CERTIFIED_WITH_PROP_SPROP_FOUNDATION` | none | none | false / false | `ACCEPTED_V06_TRANSLATION` |
| `supremum_none` | `CERTIFIED_WITH_PROP_SPROP_FOUNDATION` | none | none | false / false | `ACCEPTED_V06_TRANSLATION` |
| `supremum_in` | `CERTIFIED_WITH_PROP_SPROP_FOUNDATION` | none | none | false / false | `ACCEPTED_V06_TRANSLATION` |
| `supremum_spec` | `CERTIFIED_WITH_PROP_SPROP_FOUNDATION` | none | none | false / false | `ACCEPTED_V06_TRANSLATION` |

Thus the user's final group of 11 targets (six subadditivity declarations and
five supremum theorems) passed 11/11. The whole closure passed 17/17: one clean
`CERTIFIED` result and sixteen results explicitly carrying the approved
`PropSPropFoundation.interpret_strict` boundary.

### Assumption and provenance audit

- `semantic_premises = []` for every target.
- `unexpected_assumptions = []` for every target and common bridge.
- Target imported theorem dependency is false for every target.
- Official source theorem proof dependency is false for every theorem target.
- `neqP` does not depend on `interpret_strict`; its visible importer boundary
  is imported `Lean.eq` plus the audited local equality truth witness.
- The other sixteen new results expose `interpret_strict`, imported `Lean.eq`,
  and exact local SProp definitional-UIP markers. These are not hidden under a
  plain `CERTIFIED` label.
- Common bridges were separately printed and audited; their audit passed.
- Source compatibility passed with no failures. The sole source compatibility
  edit remains the one-line Rocq-9.3 binder syntax transformation in
  `util/seqset.v`; reversing it produces the authoritative file byte-for-byte,
  and kernel type guards check the affected declarations.
- Frozen-baseline audit passed with no mismatch. The production Lean tree hash
  remained `eecd7aa0abc1200cd777f7419c8cfb72a1b98216e2e5bfb218b7dd6157da2fde`,
  and the historical `Prosa-fei/Prosa` tree hash remained
  `d2bebcb2359b75724497d1d073fd7ed38f47ed10d282e4c6de750410146d6421`.
- No production Lean source was changed during closure.
- Final closure status artifact SHA-256:
  `48e01953bde197bb3e8f9cdc8a8e73bb35b8e959cee6350a42507bd4e6c7f1af`.
- Final closure manifest SHA-256:
  `00c06b4e243aae3d229e76daaec101a2924912e1235c74926c6319dac02f42d3`.
- Assumption summary SHA-256:
  `49cef74a225b56fc5bdb02ed520d11b6e9d129f3c76291f5dcd1ec797089d5b7`.

### Accepted files and cumulative coverage

All six Slice-2 source files are now `ACCEPTED_V06_FILE`:

- `util/notation.v`: 1/1
- `util/tactics.v`: 2/2
- `util/rel.v`: 3/3
- `util/seqset.v`: 3/3
- `util/subadditivity.v`: 6/6
- `util/supremum.v`: 7/7

Slice 2 is 22/22 accepted, comprising six `CERTIFIED` and sixteen
`CERTIFIED_WITH_PROP_SPROP_FOUNDATION` declarations. Including Slice 1, the
cumulative workspace status is:

- accepted files: 7 / 357;
- accepted declarations: 24 / 2439;
- translated but not certified: 0;
- proof-clean accepted declarations: 24;
- deferred CoqEAL boundary declarations: 239.

### Final verdict

```text
FOUNDATION_SLICE_2_CLOSURE_STATUS = PASS
READY_FOR_LAYER1_UTILS = YES
READY_FOR_JOB_FOUNDATION = NO
```

`READY_FOR_JOB_FOUNDATION` remains `NO` for a dependency reason, not a failed
certificate: the authoritative file DAG gives `behavior/job.v` direct
dependencies on `behavior/time.v` and `util/all.v`, while `util/all.v` and its
transitive prerequisites are not yet accepted. No new source file translation
was started in this closure.
