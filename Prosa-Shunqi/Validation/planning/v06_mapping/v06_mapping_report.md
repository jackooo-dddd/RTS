# Prosa v0.6 Migration and Representation Preparation Report

**Authoritative target:** Prosa v0.6 commit
`414e66760333eaa4ef78c685bcf53291c527a548`  
**Historical reference:** Prosa v0.4 commit
`ee05f255e29676ad79e07b5d6cc59dc66cd7fcb7`  
**Production Lean status:** frozen and unmodified  
**Preparation completed:** 2026-09-20 19:56:32 HKT

## Scope and method

The migration table is v0.6-centered: each of the 2,439 named public v0.6
declarations occurs exactly once. The current Lean tree and v0.4 source are
candidate/reference evidence only. File readiness continues to be determined
solely by the hardened v0.6 file DAG; declaration edges are a fine-grained aid
with documented implicit-resolution limitations.

The v0.4 inventory was regenerated from the complete pinned tree using the
same source declaration kinds, local-declaration exclusion, attributed
declaration handling, structure-field extraction, and computational
`Proof...Defined` span policy as the v0.6 inventory. It contains 317 files and
2,698 named public declarations. Because v0.4 was not rebuilt in the modern
Rocq environment, its types are explicitly marked
`SOURCE_COMMAND_FINGERPRINT_ONLY_NOT_ELABORATED`; no elaborated-type claim is
made.

Counterparts are accepted from same-file/name continuity, identical normalized
commands after a move, uniquely strong command-shape evidence, or an explicit
v0.4 structure-field ancestor. A global same name alone is retained only as an
unclear hint. Current Lean was scanned afresh; the old dashboard was not used.

## v0.4 → v0.6 evolution

| Primary classification | v0.6 declarations |
|---|---:|
| `UNCHANGED_FROM_V04` | 151 |
| `EVOLVED_SIGNATURE` | 421 |
| `EVOLVED_DEFINITION` | 32 |
| `EVOLVED_STRUCTURE` | 6 |
| `SPLIT_OR_MERGED` | 2 |
| `MOVED_OR_RENAMED` | 19 |
| `NEW_IN_V06` | 1,793 |
| `UNCLEAR` | 15 |
| **Total** | **2,439** |

Thus 151 declarations are supported as basically unchanged. There are 461
primary substantive-evolution/split rows (421 + 32 + 6 + 2), plus 19 primarily
moved/renamed rows whose secondary notes retain any simultaneous change.
There are 1,793 declarations with no credible v0.4 public/field ancestor under
the conservative matcher. Fifteen remain unclear rather than being forced into
new or evolved categories.

Here `UNCHANGED_FROM_V04` means only **normalized source declaration command
unchanged under the available evidence**. It does not mean that the final
post-Section elaborated types or semantics have been certified equal: v0.4 has
source fingerprints, whereas v0.6 additionally has actual
`Check @declaration` evidence. Accordingly, all 144
`REUSE_AFTER_REVALIDATION` rows still require fresh v0.6 type and semantic
validation and remain planning candidates, not certified translations.

No row uses `REPRESENTATION_REFORMULATION` as its primary v0.4→v0.6 class:
known representation reformulations in this workspace concern the current
Lean encoding (for example `eqType` versus `Type + DecidableEq`), while the
source declarations themselves are unchanged or structurally evolved. Those
facts are recorded in `secondary_notes`, `representation_policy`, and the
foundational decision document instead of distorting the source-evolution
classification.

The separate legacy inventory contains 2,085 v0.4 declarations not selected as
a credible ancestor of a v0.6 public declaration. This includes deleted,
replaced, and old analysis/result declarations; the label does not by itself
claim semantic obsolescence.

## Current Lean candidates and reuse decisions

Candidate provenance:

| Provenance | Rows |
|---|---:|
| `HIGH_V04_PROVENANCE` | 627 |
| `HISTORICAL_BUT_UNVERIFIED` | 8 |
| `NAME_ONLY` | 12 |
| `NONE` | 1,792 |

Reuse decisions:

| Action | Rows |
|---|---:|
| `REUSE_AFTER_REVALIDATION` | 144 |
| `ADAPT_OLD_LEAN` | 469 |
| `REFERENCE_ONLY` | 11 |
| `NEW_TRANSLATION` | 1,563 |
| `REVIEW_REQUIRED` | 13 |
| `DEFER_EXTERNAL_BOUNDARY` | 239 |
| **Total** | **2,439** |

Only 144 declarations have both strong current-Lean provenance and an
unchanged source declaration suitable for direct reuse after fresh compilation
and semantic revalidation. Another 469 have substantial reusable Lean material
but require a v0.6 delta. Eleven are reference-only. The 1,563 new-translation
rows have neither a usable candidate nor an external-boundary deferral.

No `REUSE_AFTER_REVALIDATION` row has `NAME_ONLY`, `NONE`, or missing Lean
provenance. Classic candidates are at most `HISTORICAL_BUT_UNVERIFIED` unless
separate evidence is supplied.

## Foundational findings

- `instant`, `duration`, and `work` remain natural numbers and have strong,
  unchanged candidates.
- `JobType` and `TaskType` remain `eqType`, but their Lean representation is
  fixed as carrier `Type` plus explicit `DecidableEq` at every translated
  boundary. `JobArrival`, `JobCost`, and `JobTask` therefore retain the
  appropriate equality instances even when their fields do not compare values.
  The current bare aliases require adaptation rather than automatic reuse.
- `JobArrival`, `JobCost`, and `JobTask` are simple complete class candidates;
  all fields must remain represented.
- v0.6 `ProcessorState` is a genuine structural evolution. It owns `State`, a
  finite `Core`, per-core scheduling/supply/service, and two laws. The current
  v0.4-shaped class is not a faithful v0.6 implementation.
- `scheduled_in` moved from a source class field to a derived finite
  existential; `service_in` changed from an unconstrained aggregate field to a
  derived per-core sum; `supply_in` is new.
- The downstream service chain is textually similar in places but must be
  adapted/revalidated because the meaning of `service_in` changed.
- `completes_at` has an actual changed body, including v0.6 zero-time behavior;
  the known v0.4 Lean definition cannot be retained unchanged.
- Arrival sequences retain ordered sequence semantics. Lists and finite sets
  are not conflated.

## ProcessorState decision

The approved design keeps both `State` and `Core` as fields owned by
`ProcessorState`, with `Fintype Core` and `DecidableEq Core` stored at the same
boundary. It preserves `scheduled_on`, `supply_on`, `service_on`, and both
source laws. `scheduled_in`, `supply_in`, and `service_in` remain derived
definitions. `scheduled_in` is deliberately represented as a direct computable
Boolean-or fold over `Finset.univ` (the pinned Mathlib provides no
`Finset.any`, while `Finset.toList` is noncomputable), with a proved reflection
lemma to the existential proposition. The supply/service definitions remain
finite sums.

This option is closest to the v0.6 class, avoids propagating an unrelated
external `State` parameter, and exposes exactly the observations needed by
semantic validation. A validation-only implementation compiles under Lean
4.33.1 and pinned Mathlib. The current `ProcessorState Job State` design is
rejected as the v0.6 default, though old concrete processors remain useful
adaptation references.

## Representation policy fixed for the next phase

The approved policy now covers:

- `eqType` → carrier plus `DecidableEq`;
- `finType` → carrier plus `Fintype` and `DecidableEq`;
- `seq` → `List`, distinct from extensional `Finset`;
- explicit Bool/Prop reflection boundaries;
- half-open MathComp interval sums → `Finset.Ico` value semantics;
- preservation of class/record fields, laws, and inductive constructors;
- the nested-carrier v0.6 `ProcessorState` decision.

No independent `coq-lean-mapping` skill was available in this environment.
The policy instead uses the pinned source, current/historical code inspection,
and the repository's already machine-checked semantic-validation experiments.

## Refinement boundary

All 239 `implementation/refinements/` declarations remain present. Their
v0.6 type evidence is `UNRESOLVED_EXTERNAL` because CoqEAL is unavailable, and
their reuse action is uniformly `DEFER_EXTERNAL_BOUNDARY`. No high-confidence
semantic judgment was fabricated for this group.

## Reproduction and consistency

Run:

```bash
cd Prosa-fei
./Validation/planning/v06_mapping/reproduce.sh
```

The script verifies the pinned v0.4/v0.6 commits, regenerates both inventories
and both migration-table formats, compiles the representation prototype with
Lean 4.33.1 and Mathlib commit
`0df444a360eaa60ab8c11dca51a86af692955474`, checks all 2,439 rows and the 239
external rows, audits reuse/provenance invariants, checks the production Lean
tree object before and after, and runs `git diff --check`.

## Direct answers

1. **Basically unchanged from v0.4:** 151 declarations.
2. **Substantive primary evolution:** 461 declarations; 19 additional rows are
   primarily moved/renamed and retain secondary change notes.
3. **Genuinely new under conservative evidence:** 1,793 declarations.
4. **Strong direct reuse candidates:** 144, all requiring fresh revalidation.
5. **Adapt/reference:** 469 adapt plus 11 reference-only.
6. **New translation:** 1,563; another 239 are deferred at the CoqEAL boundary.
7. **Fixed representations:** naturals, equality-bearing carriers, finite
   carriers, sequences/finite sets, Boolean reflection, interval sums,
   class/record/inductive fidelity, and `ProcessorState` Option A.
8. **Human review:** 13 current rows with unresolved historical/candidate
   ambiguity; 15 migration classifications are unclear in total, two of which
   lie in the deferred external group.
9. **ProcessorState:** nested/owned `State` and finite `Core`, with all v0.6
   per-core operations and laws; derived aggregate definitions remain outside.
10. **Readiness:** the repository is ready for translation-pipeline preparation
    and work-package design. It is not yet authorization to start production
    translation; each package must follow file-DAG order and this policy.

## Final foundational-policy corrections — 2026-09-20 19:56:32 HKT

- `UNCHANGED_FROM_V04` is now explicitly limited to unchanged normalized
  source declaration commands. It is not an elaborated-type or semantic
  certificate, and none of the 144 reuse rows was promoted to certified.
- All prototype declarations whose source carrier is an `eqType` now retain
  the corresponding `DecidableEq` evidence, including `JobArrival`, `JobCost`,
  and both carriers of `JobTask`.
- `scheduled_in` now uses a computable Boolean-or `Finset.univ.fold`. The first
  attempted `Finset.any` spelling was unavailable in pinned Mathlib, and
  `Finset.toList` was correctly rejected as noncomputable. The selected fold
  compiles without `noncomputable` and its existential truth-table lemma is
  kernel-checked by Lean.
- `ProcessorState` remains the approved nested-carrier v0.6 structure;
  `supply_in` and `service_in` remain finite sums.
- The migration CSV/JSON and summary hashes remain identical to the accepted
  Prompt 2 artifacts; no migration classification was regenerated or changed.
- Relevant checks passed under Lean 4.33.1 and Mathlib
  `0df444a360eaa60ab8c11dca51a86af692955474`; `git diff --check` passed and
  the production Lean status is empty.

```text
FOUNDATIONAL_REPRESENTATION_POLICY_READY = YES
```
