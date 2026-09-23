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
