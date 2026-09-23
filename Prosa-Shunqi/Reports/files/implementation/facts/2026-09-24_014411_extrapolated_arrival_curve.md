# `implementation/facts/extrapolated_arrival_curve.v`

Authoritative source: Prosa v0.6 commit
`414e66760333eaa4ef78c685bcf53291c527a548`.

## 2026-09-24 01:44:11 +08:00 — Rank 36 selected

After Rank 35 publication, Rank 36 is the earliest unfinished READY file in
the approved order. The authoritative file DAG gives three direct internal
dependencies (`behavior/time.v`, `util/all.v`, and
`implementation/definitions/extrapolated_arrival_curve.v`), all with existing
whole-file acceptance. The pinned source SHA-256 is
`a37288347a7501a1f4db8366816e850ffa961e6c5774ac38bfbb4fcb6d43dc1a`.
The declaration inventory contains exactly ten public lemmas, all
`NEW_TRANSLATION` in the planning mapping. They form order/sortedness,
prefix-step, and extrapolated-curve arithmetic clusters. Most underlying
operations already have Rank 33 semantic certificates, but the theorem
statements and Lean proofs are new. The operation inventory and selection
are recorded in
`Validation/planning/v06_pipeline/implementation_facts_extrapolated_arrival_curve_selection.json`.
No Rank 36 declaration is accepted yet; formal cumulative coverage remains
306/2439 declarations and 34/357 files.

## 2026-09-24 01:46:38 +08:00 — first proof cluster compiled

The first three source statements (transitivity of `ltn_steps`, reflexivity
and transitivity of `leq_steps`) were translated into a validation-only Lean
proof-development fixture. All three compile under Lean 4.33.1 against the
accepted Rank 33 implementation; `#print axioms` reports only `propext`.
This does **not** yet count as production translation or semantic acceptance.
The remaining seven lemmas use sorted-list, filter/last, and division/modulo
operations and still need proof reconstruction and actual-artifact
correspondence. The source-order target list and whole-file operation
inventory are fixed in the Rank 36 selection JSON.

## 2026-09-24 01:49:56 +08:00 — fourth Lean proof and reusable order step

The validation-only fixture now also compiles
`sorted_ltn_steps_imply_sorted_leq_steps_steps`. A small auxiliary lemma
proves the pointwise strict-to-weak Boolean step relation, and a structural
induction over `sortedBoolFrom` lifts it to ordered lists; this mirrors the
source's `sub_path` argument while retaining the actual Rank 33 sorted
definition. All four compiled fixture proofs have only Lean's approved
`propext` assumption. Six harder statements remain; the file has not yet
been written to production or semantically accepted. This is a source-order
proof-development milestone, not a status promotion.

## 2026-09-24 01:55:35 +08:00 — zero-time step proof compiled

`step_at_0_is_00` now compiles in the validation-only Lean fixture. Its
reusable local operation lemma derives that a strictly sorted tail has no
step at time zero; the proof then handles an empty list, a first step after
zero, and a first step at zero (using `no_inf_arrivals`). `#print axioms`
reports `propext` and `Quot.sound`, with no `sorryAx`. Five of the ten Lean
theorem proofs have therefore been reconstructed provisionally; none is yet
an accepted Rank 36 translation because actual-artifact semantic certificates
and whole-file publication have not run.

## 2026-09-24 02:01:03 +08:00 — value-at operation interface

A generic validation-only `getLastD(filter p xs)`/`foldl` value equation
now compiles by list induction. This is an operation-level proof, not a
new source declaration: it keeps the actual Rank 33 `step_at` result tied
to ordered List filtering and its default value. It is intended for the
`value_at_monotone` and step-change cluster so those theorems do not each
re-prove filter/last semantics. The five previously compiled public proofs
remain unchanged; semantic acceptance is still 0/10 for Rank 36.

## 2026-09-24 02:04:34 +08:00 — `value_at_monotone` Lean proof

The sixth public theorem proof now compiles in the fixture. Its computation
argument first kernel-proves that the actual `filter`+`getLastD` value equals
a left fold, then proves that the fold is monotone in time under the
source-corresponding `sorted_leq_steps` invariant. The induction handles the
four select/not-select cases without assuming the result as a premise.
`#print axioms value_at_monotone` reports only `propext` and `Quot.sound`.
The operation lemma can also support the remaining step-change proof. The
file remains unaccepted (6/10 proof-developed; 0/10 semantic acceptance).

## 2026-09-24 02:10:00 +08:00 — `step_at_agrees_with_steps_of` Lean proof

The seventh public proof now compiles in the fixture. A separate sorted-list
operation lemma shows that, for any member `(t,v)` of a strictly ordered
step list, filtering through time `t` leaves that member as the last
selected step. The proof uses constructor-preserving List induction and
the previously developed strict-tail filter fact; it does not assume the
target theorem. `#print axioms` reports only `propext` and `Quot.sound`.
Three Lean theorem proofs remain, and all ten semantic certificates still
need actual-artifact validation after a whole-file snapshot freeze.

## 2026-09-24 02:20:30 +08:00 — all ten Lean proofs reconstructed

The final two arithmetic lemmas now compile: monotonicity of the
extrapolated curve follows from the certified-definition-shaped `value_at`
operation and a quotient/remainder case split; `extrapolated_arrival_curve_change`
then distinguishes quotient growth from growth in the within-horizon value.
Together with the direct discrete-time filter argument for
`value_at_change_is_in_steps_of`, the validation-only fixture contains
proofs for **10/10** public theorem statements. `#print axioms` for each
shows no `sorryAx`; observed Lean foundations are `propext`, `Quot.sound`,
and `Classical.choice` for the finite-list existential contradiction proof.
This is proof reconstruction only. Next gate: copy this fixed candidate into
the new production module, fresh-compile/export/import the complete module,
then prove source↔target statement correspondence and audit assumptions.
Formal accepted coverage is still 306/2439 and 34/357.

## 2026-09-24 02:23:19 +08:00 — full production Lean module compiled

All ten proof-clean candidates were transferred into the single production
file `Prosa/Implementation/Facts/ExtrapolatedArrivalCurve.lean` with the pinned
source header. A project `lake build` of that module succeeded (`8728`
Lake jobs, target module built in approximately 65 seconds). This confirms
the whole-file Lean translation compiles together, but **does not** yet
certify any source↔target theorem statement. The full module is now the
frozen Rank 36 candidate for fresh export/import and Rocq semantic review.

## 2026-09-24 02:27:50 +08:00 — actual Lean and official source signatures imported

The single frozen production module exported all ten compiled theorem types
with generic statement-only mode; the `.out` is 78,390 bytes and
`rocq-lean-import` completed successfully. On the source side, the accepted
extractor generated all ten statement signatures from pinned v0.6
post-Section elaborated-type evidence, omitting proof bodies. The only
additional source operation needed was `util/rel.v`'s `monotone`, extracted
byte-for-byte from the same pinned source and independently compiled.
`OfficialExtrapolatedArrivalCurveFacts.v` now compiles under Rocq 9.3, with
the Rank 33 official definition slice and behavior/time module; the first
attempt lacked the non-reexported `duration` import and failed, then an
explicit `Require Import prosa.behavior.time.` resolved this source-loading
issue without changing any statement. The next step is compositional
theorem-statement correspondence. No Rank 36 semantic certificate has
passed yet; formal coverage remains 306/2439 and 34/357.

## 2026-09-24 02:36:52 +08:00 — accepted operation DAG reused on combined artifact

A validation-only combined export root now includes (i) the **exact compiled
types** of all ten Rank 36 theorems in statement-only mode, (ii) the Rank 33
computational definitions, and (iii) four proof-bodied Euclidean arithmetic
interface lemmas. The combined `.out` imported successfully into Rocq. An
audited generator verified the accepted Rank 33 operation-certificate source
hash (`962be17e…`) against its published manifest, changed only the
artifact-local imported-module qualifier (266 occurrences), and compiled
the generated Rocq proof against the combined import. This is **not** an
assumed cross-artifact equivalence: Rocq rechecked the full lower-level
correspondence proof with the new actual imported constants. The first
attempt lacked the common imported Subadditivity foundation loadpath; adding
the previously accepted module resolved it, with no proof change. The ten
Rank 36 theorem-shell certificates and final assumption audit are still open.

## 2026-09-24 02:43:33 +08:00 — first three theorem-shell certificates compiled

The shared structural relation for step-pair predicates now compiles against
the combined actual Lean artifact. It composes the rechecked Rank 33
`ltn_steps`/`leq_steps` and Boolean-truth correspondences, with bidirectional
step decoding, to certify the exact statements of
`ltn_steps_is_transitive`, `leq_steps_is_reflexive`, and
`leq_steps_is_transitive`. Rocq `Print Assumptions` for all three shows only
the already audited importer foundations and
`PropSPropFoundation.interpret_strict`; no new semantic premise or target
theorem constant is used. This is **3/10 provisional Rank 36 statement
correspondences**, not whole-file acceptance. Formal coverage remains
306/2439 declarations and 34/357 files. The remaining seven statements
combine prefix predicates, arithmetic, membership, and extrapolated-value
operations.

## 2026-09-24 02:47:59 +08:00 — six structural correspondences compile

The same compiled Rocq certificate file now also checks
`sorted_ltn_steps_imply_sorted_leq_steps_steps`, `value_at_monotone`, and
`extrapolated_arrival_curve_is_monotone`. These reuse the already checked
prefix predicates, Nat `≤`, `value_at`, and extrapolated-curve operation
correspondences through two shared logical-relation shells. The exact
compiled Lean theorem types were inspected in the combined importer
environment before composing the proofs. `Print Assumptions` reports only
the previously declared Prop/SProp and importer foundations; no target
proof or new semantic premise was used. **6/10** Rank 36 theorem-statement
correspondences are provisional; no Rank 36 declaration is yet formally
published. Four statements remain: pair equality/membership, existential
membership, and the quotient/remainder change proposition.

## 2026-09-24 02:51:51 +08:00 — pair equality and membership bridges close two more statements

An operation-level pair equality relation and ordered pair-list membership
relation now compile against the actual combined imported Lean artifact.
The latter is an induction over imported `List.Mem` constructors and keeps
MathComp sequence order/multiplicity; it is not a theorem-specific premise.
They compose with the previously certified `step_at`, `steps_of`, and sorted
predicate relations to compile `step_at_0_is_00` and
`step_at_agrees_with_steps_of`. The certificate file now checks **8/10**
Rank 36 theorem-statement correspondences, all provisional pending exact-type
and fail-closed publication audit. The two remaining statements are
`value_at_change_is_in_steps_of` (existential membership) and
`extrapolated_arrival_curve_change` (quotient/remainder disjunction).

## 2026-09-24 02:56:58 +08:00 — all ten statement correspondences compile

The remaining existential-membership theorem and quotient/remainder
disjunction theorem now compile as structural source↔actual-imported-target
relations. For the former, the imported `Exists` witness is transported
through the certified pair-list membership relation; for the latter, the
certificate composes the Rank 33 add/div/mod/value/curve relations with
Nat disequality, equality, order, conjunction, and disjunction relations.
The imported target theorem constants and official source theorem proof
constants are not used in these correspondence proofs. All ten `Print
Assumptions` outputs show only previously audited importer UIP-related
foundations and `PropSPropFoundation.interpret_strict` (with `propext` in
some operation paths); no new semantic premise appears. **10/10 is still
provisional** until exact-type binding, fail-closed automatic assumption
audit, source/Lean provenance, and whole-file publication pass. Cumulative
formal coverage remains 306/2439 and 34/357.

## 2026-09-24 03:05:17 +08:00 — exact-type and fail-closed audits pass

Separate Rocq guards now check, for each of the ten declarations, that the
certificate's source proposition is definitionally equal to the pinned
post-Section source signature and that its target proposition is exactly the
type of the corresponding actual imported Lean theorem constant. All 20
guards compiled; the target constants are used **only in this provenance
guard file**, never in the semantic certificate. The existing fail-closed
assumption classifier processed ten marked `Print Assumptions` sections:
10/10 `CERTIFIED_WITH_PROP_SPROP_FOUNDATION`, zero semantic premises,
zero statement-only transitive theorem dependencies, zero source/target
self-dependencies, and zero unexpected assumptions. Official source
extraction was rerun from the clean pinned checkout and reproduced the
source signature file byte-for-byte (SHA-256 `5865d8dd…`). A separate
isolated Lean compilation of the frozen production source succeeded; its
`.olean` hash differs from the project build due to output-path/build
configuration, so byte identity is **not** claimed. The actual exported
artifact still comes from the project build made after the source file was
frozen. A fresh `#print axioms` audit of all ten Lean proofs completed with
only the approved Lean foundations (`propext`, `Quot.sound`, and where
needed `Classical.choice`), no `sorryAx`. Whole-file content-addressed
publication remains to be done; cumulative accepted coverage is still
306/2439 and 34/357.

## 2026-09-24 03:09:04 +08:00 — whole-file publication accepted

The content-addressed publisher checked the ten-declaration source inventory,
clean pinned source checkout, accepted direct file dependencies, frozen
production Lean source and compiled artifact chronology, exact 10-target
statement-only export, 21 accepted computational bodies and four
proof-bodied arithmetic interfaces, Rocq import, source replay, all 20
source/target type guards, ten proof-clean Lean audits, and all ten
fail-closed semantic assumption records. It then published
`implementation_facts_extrapolated_arrival_curve_module_manifest.json` and
`..._status.json` with `ACCEPTED_V06_FILE`. All ten declarations have
`ACCEPTED_V06_TRANSLATION` and
`CERTIFIED_WITH_PROP_SPROP_FOUNDATION`; no semantic premise, target/source
theorem self-dependency, transitive statement-only theorem dependency, or
unexpected assumption remains. The foundation boundary is explicitly
`PropSPropFoundation.interpret_strict`, alongside audited importer
foundations. Formal cumulative coverage is now **316/2439 declarations,
35/357 files**, with zero translated-but-not-certified in this published
snapshot. This closes Rank 36; the next file must be chosen from the current
machine status and authoritative file DAG.
