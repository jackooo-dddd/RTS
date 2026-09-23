# `implementation/definitions/extrapolated_arrival_curve.v`

## 2026-09-23 21:11:29 +08:00 — selection and operation inventory

Rank 33 in the approved order, layer 4 in the authoritative file DAG. Its
direct dependencies are accepted `behavior/time.v` and `util/all.v`, so the
file is READY. The pinned official source at commit
`414e66760333eaa4ef78c685bcf53291c527a548` has 21 public declarations
in 146 lines (source SHA-256
`73ed41bb13c2e006ffe0abc9cc22aec08a17eadde1e7348669897fa74e94f38c`).
The migration table classifies all 21 as `NEW_TRANSLATION`; no historical
Lean file is being treated as a trusted candidate.

The pre-freeze operation inventory identifies an ordered list of
duration/value pairs, pair projections, filtering, last-with-default, Nat
division/modulo (including zero denominator), Bool membership/all, and
adjacent sortedness. Existing accepted List/Nat/division/reflection bridges
are candidates for reuse but must be checked against this new imported
artifact. `large_horizon_P` and `valid_arrival_curve_prefix_P` are source
`reflect` views in an informative sort; replacing them with an unqualified
`Prop` iff would be a representation decision, not a mechanical translation.
The initial target scope and every source declaration are frozen in
`Validation/planning/v06_pipeline/implementation_extrapolated_arrival_curve_selection.json`.

No production declaration for this file is accepted yet. Formal project
coverage remains **281/2439 declarations, 31/357 files**.

## 2026-09-23 21:21:33 +08:00 — whole-file Lean candidate compiles

`Prosa/Implementation/Definitions/ExtrapolatedArrivalCurve.lean` now contains
counterparts for all **21/21** public source declarations plus four labeled
helpers: two ordered adjacent Boolean sortedness operations, a
constructor-preserving `BoolReflect` view, and `large_horizon_iff`.
`lake env lean` passes under the pinned Lean 4.33.1 project.
This is **translation/proof compilation only**, not semantic acceptance.

The first compile exposed a substantive representation issue: Lean `theorem`
cannot have the informative `BoolReflect ...` type, while the official Rocq
`reflect` lemmas do. They are therefore Lean `def` proofs of a corresponding
indexed data type, not erased to an arbitrary `Prop` iff. A second compile
found that case-splitting on the full `large_horizon` proposition required
noncomputable `Classical.propDecidable`; the final proof instead splits the
computed Boolean result and uses a separately proved `large_horizon_iff`.
No production `sorry`, custom axiom, or semantic premise was added.

Next: inspect the actual compiled computation interface and establish
artifact-local product/list/sorted/reflect relations, then fresh export/import
and Rocq certificates. The file is **not accepted**; formal cumulative
coverage remains **281/2439 declarations, 31/357 files**.

## 2026-09-23 21:35:48 +08:00 — compiled computation preflight

The validation-only `ExtrapolatedArrivalCurvePreflight.lean` imports the
compiled production module. Lean kernel accepted `rfl` guards for all three
adjacent-sortedness equations: empty tail, nonempty tail, and the public
`sortedBool` wrapper. The compiled implementation internally uses
`List.brecOn`, but the required source-facing recursive equations reduce
definitionally. The first test run failed only because the test expression
needed parentheses around a Boolean `&&` right-hand side; the corrected run
passed. This checks the actual compiled computation interface, not yet a
Rocq↔Lean semantic correspondence.

Preliminary `#print axioms` on `large_horizon_iff`, `large_horizon_P`, and
`valid_arrival_curve_prefix_P` reports only standard Lean `propext` and
`Quot.sound`. This is not yet the final whole-file proof or assumption audit.
All 21 declarations remain **unpublished / not semantically accepted**.

## 2026-09-23 21:41:02 +08:00 — first actual-artifact import

The compiled Lean module's first eight computational declarations were
exported by the pinned `lean4export` into
`ExtrapolatedArrivalCurveBase.out` (SHA-256
`7784434ab897c30337337c79211498c3300326bf381c12356b0003f458423880`).
The pinned Rocq 9.3 importer successfully compiled
`ImportedExtrapolatedArrivalCurveBase.v`; the resulting `.vo` SHA-256 is
`62cb35af54a45b27a31ace5e7334f860b4b866426b129b6fdd3a76f0e2a78f20`.
The import ended with 198 entries, including the actual target
`ArrivalCurvePrefix`, `step_at`, `value_at`, and
`extrapolated_arrival_curve` bodies. The official v0.6 blocks for the same
eight definitions were automatically extracted, with elaborated evidence,
and compiled under Rocq 9.3 (`OfficialExtrapolatedArrivalCurveBase.vo`, SHA-256
`fd20370108f690447ca38c7045851fe4fe3081462d939e2b913f3ca1ba5f3334`).
The only source-loading adjustment was replacing the two `Require Export`
commands with the already-certified `behavior/time.v` and direct MathComp
imports; none of the eight extracted definition commands was edited.

This establishes working source and target artifacts, **not** yet a semantic
certificate. Next obligation: pair/list representation and value-preservation
relations for these actual imported declarations, followed by whole-file
export of the remaining 13 declarations and fail-closed audits. Formal
coverage remains **281/2439 declarations, 31/357 files**.

## 2026-09-23 21:46:57 +08:00 — first three composition certificates

`ExtrapolatedArrivalCurveBaseCorrespondence.v` now defines a representation
map for the actual imported Lean `Prod_inst3` and ordered `List_inst1`, reusing
the already-certified Nat conversion. Rocq kernel compiled three independent
operation certificates for `inter_arrival_to_prefix`, `horizon_of`, and
`steps_of`; their propositions directly name the imported constants, not a
handwritten target model. The automatic `Print Assumptions` classifier reports
`CERTIFIED` for each with `semantic_premises=[]`, source/target self-dependency
false, statement-only dependencies `[]`, unexpected assumptions `[]`, and no
Prop/SProp bridge. The only visible foundation is the imported `Lean.eq`
(reported by Rocq as definitional UIP).

These are **provisional per-declaration certificates**, not yet published
`ACCEPTED_V06_TRANSLATION`: the full 21-target export, source-binding/type
guards, Lean proof audit, whole-file regression, and content-addressed
publication are still outstanding. The three results do not change formal
coverage (**281/2439, 31/357**). Next work is to extend the pair/List
operation interface for `time_steps_of`, `step_at`, and `value_at`, while
preserving list order and multiplicity.

## 2026-09-23 21:49:00 +08:00 — mapped-list operation reused

Added `time_steps_of` to the same actual-artifact correspondence certificate.
The proof inducts over the source ordered sequence and reuses the imported
product/list constructor relation; it does not assume `List.map` semantics.
Rocq kernel compilation and the marked, fail-closed assumption audit pass for
all four current base certificates (`inter_arrival_to_prefix`, `horizon_of`,
`steps_of`, `time_steps_of`). Each reports `CERTIFIED`, with no semantic
premise, no theorem self-dependency, no unexpected assumption, no statement-
only dependency, and only the visible imported `Lean.eq` foundation.

The next genuinely new operation is `step_at`: MathComp filtered ordered
sequence plus `last` must correspond to imported Lean `List.filter` plus
`getLastD`, including the Boolean Nat-≤ decision. Until that operation bridge
and the remaining declarations are checked, **none of this file's 21
declarations is in the published acceptance count**.

## 2026-09-23 22:18:08 +08:00 — `step_at` correspondence closed

The first difficult computational target is now kernel-proved against the
actual imported Lean body. The proof composes an artifact-local ordered
`filter` relation (retaining multiplicity), imported `getLastD` equations for
empty/singleton/longer lists, the imported pair constructors, and the existing
Nat-≤/Boolean decision relation. The imported `List.filter` uses `List.brecOn`
internally, but its `nil`/`cons` equations and all `getLastD` equations were
proved by Rocq definitional reduction (`Lean.eq_refl`), not assumed. The first
attempt got stuck when MathComp expanded a concrete `leq` predicate during
case splitting; abstracting the predicate yielded one reusable generic filter
lemma, instantiated for `step_at`.

The marked, fail-closed `Print Assumptions` audit reports
`eac_step_at_correspondence` as
`CERTIFIED_WITH_PROP_SPROP_FOUNDATION`: semantic premises `[]`, source/target
self-dependencies false, statement-only dependencies `[]`, unexpected `[]`.
Its visible foundation is `PropSPropFoundation.interpret_strict` plus the
existing imported equality/UIP boundary. The previous four certificates
remain `CERTIFIED` without that Prop/SProp axiom. This is still a provisional
per-declaration result: final source-binding/type audit, the remaining 16
declarations, whole-file regression, and publication are open. Formal
coverage remains **281/2439 declarations and 31/357 files**.

## 2026-09-23 22:31:37 +08:00 — `value_at` and whole-file import

`eac_value_at_correspondence` now composes the certified `step_at` result with
the imported pair-second projection. Rocq kernel compilation and the marked
automatic `Print Assumptions` audit pass: status
`CERTIFIED_WITH_PROP_SPROP_FOUNDATION`; semantic premises `[]`, source/target
theorem dependencies false, statement-only dependencies `[]`, unexpected
assumptions `[]`. This is the sixth **provisional** base-slice certificate.

Separately, the complete 21-target actual Lean artifact was exported to
`Validation/.work/experiments/extrapolated_full/ExtrapolatedArrivalCurve.out`
(321 KiB) and successfully imported as
`ImportedExtrapolatedArrivalCurve.vo` by Rocq 9.3. The six certificates above
still refer to the smaller earlier base artifact; they must be rebound and
rechecked against the whole-file artifact before publication. The official
source type guards, the other 15 correspondences, full Lean proof audit, and
whole-file acceptance remain open. Published coverage is unchanged:
**281/2439 declarations; 31/357 files**.

## 2026-09-23 22:35:18 +08:00 — complete source signature and import

The full 21-declaration export imported successfully (Rocq exit 0): export
SHA-256 `8e69a2442995902c612bd8f3f1758965f6c5cd264742e260188739f96270be4a`,
imported `.vo` SHA-256
`d2b8d4f60bf86af890a6d14bbbe178f3b7f2a0e6f6f1df08654527775a9c3fb3`.
The official-source extractor then generated a 21-entry source signature from
the pinned v0.6 commit. All 19 computational declaration blocks have
byte-identical source/generated hashes; the two informative `reflect` views
retain `Type` (not a weakened Prop/Boolean equivalence) using verified
post-Section type evidence. The generated source compiled in Rocq 9.3 (exit
0), with `.vo` SHA-256
`d299cb5813052064a0368c19c506e7144526faeffafdf9024c25e4984947a94f`.
Only the two source imports through `util/all` were replaced by the minimal
required direct MathComp, `behavior/time`, and `util/epsilon` imports;
declaration bodies/statements were not rewritten.

This closes the full-artifact import and source-acquisition setup, **not** the
full semantic certificate. The six existing proofs still name the smaller
actual-artifact import and must be checked against this full import (or given
an audited artifact-identity adapter). The remaining 15 declarations and
whole-file publication remain open; accepted coverage is unchanged.

## 2026-09-23 22:41:04 +08:00 — seven proofs rebound to full artifact

Recompiled the six earlier operation certificates against the **complete**
imported `ImportedExtrapolatedArrivalCurve` module and complete extracted
official source signature, rather than carrying their smaller-artifact result
forward by assertion. Their definitions/proofs were mechanically adapted to
the new artifact-local names and all recompiled. Added
`eac_positive_horizon_correspondence`, composing the existing horizon relation
with the certified Nat-`<`/Boolean-decision bridge. Its imported target body
was inspected: it is `Decidable_decide (0 < horizon_of ac_prefix)`.

The marked full-artifact `Print Assumptions` audit now classifies seven
certificates: `inter_arrival_to_prefix`, `horizon_of`, `steps_of`,
`time_steps_of` as `CERTIFIED`; `step_at`, `value_at`, `positive_horizon` as
`CERTIFIED_WITH_PROP_SPROP_FOUNDATION`. Each has `semantic_premises=[]`,
`unexpected=[]`, no source/target theorem self-dependency, and no
statement-only dependency. This remains **provisional**: 14 source
declarations, the whole-file type/proof regression, and publication are not
done. Published coverage remains **281/2439; 31/357**.

## 2026-09-23 22:43:59 +08:00 — Boolean equality reused for `no_inf_arrivals`

Added a small operation-level `Nat == Nat` ↔ imported `Decidable_decide
(Lean.eq ...)` adapter by composing the existing certified Nat equality
relation with MathComp `eqP` reflection. Then
`eac_no_inf_arrivals_correspondence` composes that adapter with the already
audited `value_at` relation at time zero. The actual imported target body was
inspected before proving it. Rocq compilation and the marked automatic
assumption audit pass, with
`CERTIFIED_WITH_PROP_SPROP_FOUNDATION`, semantic premises `[]`, theorem
self-dependencies false, statement-only dependencies `[]`, unexpected `[]`.
There are now **8 provisional full-artifact certificates**; 13 declarations
still lack correspondence, and the file remains unpublished.

## 2026-09-23 22:47:51 +08:00 — paired-step comparisons

`ltn_steps` and `leq_steps` now have full-artifact correspondence certificates.
Both reuse the existing imported Nat `<`/`≤` Boolean-decision relations,
the source-pair ↔ imported-pair relation, and one newly proved artifact-local
Boolean conjunction operation lemma. The actual compiled `ltn_steps` body was
inspected; it performs exactly two `Nat_decLt` decisions followed by
`Bool_and`. Both new certificates compile in Rocq and pass the marked
assumption classifier as `CERTIFIED_WITH_PROP_SPROP_FOUNDATION`, with no
semantic premise, source/target theorem self-dependency, statement-only
dependency, or unexpected assumption. The same operation relation is ready
for the two `sorted_*_steps` declarations, pending the sorted-list bridge.
There are now **10 provisional full-artifact certificates; 11 remain**.

## 2026-09-23 23:55:00 +08:00 — resumed full-artifact audit and prefix isomorphism

After resuming, the marked `Print Assumptions` classifier was rerun against
the complete imported artifact. The three previously compiled but unaudited
`large_horizon_dec`, `sorted_ltn_steps`, and `sorted_leq_steps` certificates
all pass with no semantic premise, source/target self-dependency,
statement-only dependency, or unexpected assumption. They use the recorded
`PropSPropFoundation.interpret_strict` boundary.

The `ArrivalCurvePrefix` alias now has a two-sided, actual-artifact
representation certificate. The Rocq-to-imported map preserves the horizon
and the ordered sequence of Nat pairs; an imported-to-Rocq decoder is proved
to be its inverse in both directions, including every imported list value.
Both roundtrip proofs compile under Rocq 9.3 and pass the fail-closed
assumption classifier as `CERTIFIED` with only the imported equality/UIP
foundation. This is a genuine carrier isomorphism, not a single example or a
manual replacement of the imported target type.

Current **provisional full-artifact progress is 14/21 declarations** (15
audited certificates because the alias has two roundtrip directions).
Seven declarations still require semantic correspondence:
`extrapolated_arrival_curve`, `large_horizon`, `large_horizon_P`,
`specified_bursts`, `valid_arrival_curve_prefix`,
`valid_arrival_curve_prefix_dec`, and `valid_arrival_curve_prefix_P`.
Whole-file exact-type/proof regression and publication have not run;
formal acceptance remains **281/2439 declarations and 31/357 files**.

## 2026-09-24 00:00:35 +08:00 — `specified_bursts` correspondence

The new artifact-local operation bridge relates MathComp ordered-sequence
membership to the **actual imported** Lean `List.Mem` on `Lean.Nat`. It proves
both directions using list constructors, source `eqP`, imported membership
constructors, Nat conversion and the existing Prop/SProp foundation. The
public `specified_bursts` certificate then composes that bridge with the
already audited `time_steps_of` correspondence and the exact imported
`Decidable.decide` instance. The source `ε` elaborates to `S O`, matching the
target's compiled Nat one; no Finset or hand-written target model is used.

Rocq compilation passed. The first automatic assumption audit correctly
rejected two previously unlisted foundations exposed by the imported
membership decider: `ImportedExtrapolatedArrivalCurve.propext` and
`ImportedExtrapolatedArrivalCurve.Quot_sound`. Both are existing audited Lean
logical foundations in this project, so the allowlist was extended with
those **exact names only**. The rerun passes as
`CERTIFIED_WITH_PROP_SPROP_FOUNDATION`, with `semantic_premises=[]`, no
source/target theorem self-dependency, no statement-only dependency, and no
unexpected assumption.

Provisional full-artifact correspondence is now **15/21 declarations**;
six remain (`extrapolated_arrival_curve`, `large_horizon`, `large_horizon_P`,
`valid_arrival_curve_prefix`, `valid_arrival_curve_prefix_dec`, and
`valid_arrival_curve_prefix_P`). Whole-file publication remains pending;
formal project coverage is unchanged at **281/2439, 31/357**.

## 2026-09-24 00:07:31 +08:00 — compositional predicate closure

`large_horizon` is now related bidirectionally to the exact imported Lean
predicate. The proof uses the independently audited ordered Nat-list
membership bridge, the certified Nat-`≤` relation, and the existing
`time_steps_of`/`horizon_of` certificates; it does not invoke either public
theorem proof. Two further certificates compose the five already-established
component relations into `valid_arrival_curve_prefix` (nested Prop/SProp
conjunction) and `valid_arrival_curve_prefix_dec` (left-associated Boolean
conjunction). All three compile in Rocq and pass the marked, fail-closed
assumption audit with no semantic premise, theorem self-dependency,
statement-only dependency, or unexpected axiom. The Prop/SProp foundation
remains explicitly visible where used.

Provisional progress is **18/21 declarations**. Remaining: the arithmetic
definition `extrapolated_arrival_curve` and the two informative views
`large_horizon_P` and `valid_arrival_curve_prefix_P`. Whole-file regression
and publication are still required; cumulative accepted coverage remains
**281/2439 declarations, 31/357 files**.

## 2026-09-24 00:20:22 +08:00 — informative-view statements and final arithmetic gap

The two source `reflect` theorem statements now have kernel-checked,
bidirectional **type-level** correspondence with the actual imported Lean
`BoolReflect` result types. Generic constructor-preserving maps handle
`ReflectT`/`ReflectF` and imported `isTrue`/`isFalse`, using the already
audited predicate and Boolean relations. Exact imported target types were
checked in Rocq; neither source nor imported target proof constant occurs in
the semantic certificate. Both new certificates pass the marked assumption
audit. This closes 20/21 provisional declaration correspondences.

The remaining `extrapolated_arrival_curve` definition uses MathComp `%/` and
`%%` versus imported Lean `/` and `%`. An attempted direct `rfl` adapter to
the already accepted `DivModCorrespondence` **failed**: the same Lean Nat
operations have separate artifact-local Rocq constants in the DivMod and
ExtrapolatedArrivalCurve imports. The failed adapter was removed, and the
20/21 certificate file was recompiled and re-audited successfully. The
existing DivMod proof cannot simply be named as if the two imported operators
were definitionally identical. The next step is a minimal validation-only
Euclidean computation interface exported together with this exact target
artifact, followed by a reusable quotient/remainder relation. No semantic
premise or axiom was introduced. Formal publication remains 281/2439,
31/357.

## 2026-09-24 00:31:17 +08:00 — final computational correspondence compiled

The validation-only Lean arithmetic interface compiled against the **actual
production ExtrapolatedArrivalCurve module**. Its four Euclidean laws (`div`
decomposition, remainder bound, zero-divisor quotient, zero-divisor remainder)
were exported with Lean proof bodies in a new combined `.out`, then imported
successfully into Rocq 9.3. Rocq `Check` confirmed that these laws refer to
the same artifact-local `Nat.div`/`Nat.mod` constants as the production
definition, rather than to the earlier DivMod artifact.

Using MathComp `edivn_eq`, the four imported proof terms, and the accepted
Nat/add/mul/order/equality relations, Rocq compiled a two-case (`h=0` and
`h>0`) quotient/remainder correspondence. It then compiled
`eac_extrapolated_arrival_curve_correspondence`, compositionally using the
previously proved `horizon_of` and `value_at` relations. This makes **21/21
provisional correspondences compile** against the full actual-artifact
import. This is not yet formal whole-file acceptance: the new combined
artifact still needs complete `Print Assumptions` classification, provenance,
regression, and publication. The official accepted total remains
281/2439 declarations and 31/357 files until those gates pass.

## 2026-09-24 00:41:40 +08:00 — full 21-target audit and source replay

The fail-closed `Print Assumptions` classifier passed for all **21 target
declarations** (22 certificate entries because the prefix carrier has two
roundtrips): 5 targets are `CERTIFIED` without the Prop/SProp foundation and
16 are `CERTIFIED_WITH_PROP_SPROP_FOUNDATION`. The final arithmetic target has
`semantic_premises=[]`, `statement_only_dependencies=[]`, both source/target
theorem-dependency flags false, and `unexpected=[]`. Its visible trusted
boundary includes the existing `interpret_strict`, importer equality/UIP, and
imported Lean `propext`; no new semantic axiom was added.

The exporter was rerun through the checked-in config for the combined
production+arithmetic interface; it produced a byte-identical `.out`
(`ad0ee5fb84697fc302608459e238c42d69738522c6119aa2b969d9237aa03686`)
to the artifact used by the successful Rocq import. The source extractor was
rerun from clean pinned commit `414e667…`; its regenerated full source
signature has **no diff** from the one compiled for the certificates. The
computational declaration blocks are byte-identical to official source;
theorem statement signatures use the recorded elaborated Rocq type evidence.
Lean proof audit of the production informative views passed with only standard
`propext`/`Quot.sound`; the four validation-only Euclidean facts have Lean
proof bodies, with only `propext` reported by `#print axioms` where applicable.

Still pending before publication: bind all hashes and audit evidence in a
formal Rank 33 manifest/status, run baseline/integrity checks, then update
cumulative coverage. No earlier formal acceptance count has been changed yet.

## 2026-09-24 00:47:08 +08:00 — formal whole-file publication

The Rank 33 fail-closed publisher passed after checking the 21-name official
inventory and source order, clean pinned source checkout, byte-identical
source-extraction replay, exact Lean/Mathlib/Rocq versions, Lean proof-axiom
logs, configured 25-target export (21 production declarations plus four
proof-bodied validation-only arithmetic laws), imported module identity,
all 22 certificate audit entries, and the prior published baseline. The
machine status is `ACCEPTED_V06_FILE`: **21/21 accepted** (5 `CERTIFIED`, 16
`CERTIFIED_WITH_PROP_SPROP_FOUNDATION`), with no semantic premise,
statement-only dependency, theorem self-dependency, or unexpected assumption.

The published snapshot ID is
`fe52f3d43562a868a5935d80cfaa00cac93f17f6187053f7dd87d71707b4ed82`.
Key SHA-256 evidence: production `.olean`
`108aa834c6b39d4060c7affcff9f16db509805117ec23b50d2911d163d3d56fe`,
export `.out`
`ad0ee5fb84697fc302608459e238c42d69738522c6119aa2b969d9237aa03686`,
imported Rocq `.vo`
`fee9039bc872a931bab22725f31c67abb2e9ad5c78df688a23a51e8f30a7a8e8`,
and correspondence `.vo`
`82053fc0b01048478d77bb7eb64b8e83369eb022383b058e2da9683e6fa04b46`.
Full hashes and per-declaration statuses are in
`Validation/planning/v06_pipeline/implementation_extrapolated_arrival_curve_module_manifest.json`
and its paired status JSON. Formal cumulative coverage is now
**302/2439 declarations and 32/357 files**, with zero published
translated-but-uncertified declarations. The independent rank-30
`util/lcmseq.v` blocker remains unchanged.
