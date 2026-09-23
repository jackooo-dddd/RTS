# `util/superadditivity.v` translation and validation history

Canonical report for pinned Prosa v0.6 `util/superadditivity.v` at commit
`414e66760333eaa4ef78c685bcf53291c527a548`.

## 2026-09-23 16:03:37 — selected at execution rank 32

The authoritative file DAG places this 218-line source at layer 2, with
`Require Export` dependencies on `util/list.v`, `util/nat.v`, and
`util/rel.v`; all three are already accepted. The complete source inventory
contains 12 public declarations, all classified `NEW_TRANSLATION` in the
v0.6 migration table. Selection details are in
`Validation/planning/v06_pipeline/util_superadditivity_selection.json`.

The first nine declarations are Nat-function superadditivity definitions and
facts; the final three involve the ordered `index_iota 1 h` sequence,
`max0`, and a minimal extension at one horizon. This file is independent of
the unresolved `lcmseq` and `fixpoint` branches, so work can proceed without
claiming either of those files accepted. Current state: **0/12 translated,
0/12 accepted**. No production file has been created for this source yet.

## 2026-09-23 16:11 — all Lean candidates and proofs compile

`Prosa/Util/Superadditivity.lean` now contains counterparts for all **12/12**
public source declarations. `lake env lean -DautoImplicit=false
Prosa/Util/Superadditivity.lean` passed with no placeholder or axiom. The
first four definitions retain the source's pointwise/until/global/standard
predicates; `minimal_superadditive_extension` maps the ordered
`index_iota 1 h` sequence and applies the previously accepted `max0`.
All seven theorem proofs compile. The horizon-extension proof required
distinguishing the `h=0` and zero-summand cases; the nonzero case uses the
existing `List.in_max0_le` theorem and an explicit membership witness in
the half-open `index_iota` range. This is a Lean proof smoke check only:
**0/12 semantically accepted**, no fresh export/import, Rocq certificate,
assumption audit, or whole-file publication yet.

## 2026-09-23 20:16:23 +08:00 — isolated fresh Lean rebuild and proof audit

Resumed from the existing 12-declaration candidate without changing it. An
isolated `CLEAN_FULL` Lean build compiled its complete local Prosa import
closure (`Tactics`, `Nat`, `Rel`, `Supremum`, `List`, then
`Superadditivity`) and sealed a source/artifact build manifest under
`Validation/.work/runs/translation_order_superadditivity.14gYTa/`.
The validation-only `SuperadditivityTypeAudit.lean` confirms the five
definition types and prints axiom dependencies for all seven theorem proofs:
only `propext` and `Quot.sound` occur; the equivalence proof has none.
This closes the fresh Lean compile/proof-clean preflight, **not** the Rocq
semantic gate. Next: export/import this exact artifact, acquire pinned Rocq
statements, and construct correspondence certificates.

## 2026-09-23 20:19:53 +08:00 — actual-artifact import and first definition certificate

The fresh compiled Lean artifact exported successfully (48,977 bytes,
SHA-256 `0561bdd978ad57a286e6a592cc35c5c708c5dc9cfbfbac3d37b6e07842f1dcf0`)
and `rocq-lean-import` loaded all 119 entries. Pinned v0.6 source extraction
copied the first four computational declaration blocks byte-for-byte; that
source slice compiled under Rocq 9.3. The first independent correspondence,
`SuperadditivityBaseCorrespondence.superadditive_at_correspondence`, now
kernel-compiles against the **actual imported**
`Prosa_Util_Superadditivity_superadditive_at` body. It composes the established
Nat/function/add/equality/order bridges. `Print Assumptions` shows the
approved `interpret_strict` Prop/SProp boundary, not a semantic premise.
This is an operation-level result; exact-type/audit/publication for the
12-declaration whole file are still open.

## 2026-09-23 20:23:45 +08:00 — five declaration correspondences audited

The four source-extracted computational predicates (`superadditive_at`,
`superadditive_until`, `superadditive`, `superadditive_standard`) now each have
an independent two-way Rocq correspondence proof against the imported
compiled Lean definition. The theorem
`superadditive_standard_equivalence` now also has an independently composed
statement certificate: it uses the already certified predicate relations,
never the source theorem proof or imported target theorem proof. A separate
Rocq exact-type guard typechecked the actual imported theorem constant.

Automated fail-closed `Print Assumptions` audit reports **5/5** as
`CERTIFIED_WITH_PROP_SPROP_FOUNDATION`: semantic premises `0`, statement-only
dependencies `0`, source/target self-dependency `false`, unexpected assumptions
`0`. The five are machine-checked *declaration results* but **not yet
published/accepted** as a whole file; seven declarations (including the
`index_iota`/`max0` extension) remain to validate.

## 2026-09-23 20:27:34 +08:00 — arithmetic theorem statements added

Two more official statements, `superadditive_first_zero` and
`superadditive_leq_mul`, now have structural source↔imported-Lean certificates.
They reuse the four predicate correspondences and the existing Nat equality,
multiplication, and order bridges; neither original theorem proof is used.
Separate exact-type guards accepted both actual imported theorem constants.
The automatic audit now passes **7/7** completed declaration certificates,
all `CERTIFIED_WITH_PROP_SPROP_FOUNDATION`, with no semantic premises,
statement-only dependencies, self-dependencies, or unexpected assumptions.
Five of the file's twelve declarations still lack correspondence certificates,
so the formal accepted count remains unchanged.

## 2026-09-23 20:35:18 +08:00 — monotonicity boundary closed, nine audited

`superadditive_unbounded` is now kernel-proved through a reusable
artifact-local Nat-existential relation. The `superadditive_monotone`
correspondence was also structurally proved using the official `util/rel.v`
source definition and the imported Lean `Decidable.decide`/Bool observation.
The first export (`statement_only = ["*"]`) made that proof depend on two
statement-only `Nat.decLe` helper facts. A second export kept only the seven
*target* theorem proofs statement-only and imported the transitive helper
proof bodies. It exported 103,391 bytes and imported 157 declarations; fresh
recompilation of the same correspondence removed both statement-only
dependencies. This changes only validation export configuration, not
production Lean or source semantics. The source extractor now records a
validation-only replacement import so that pinned `util/rel.v` can be loaded
without dragging unrelated legacy `util/list.v` into the source slice.

The new exact-type guard passed. Automated `Print Assumptions` audit now
reports **9/9** completed declarations as
`CERTIFIED_WITH_PROP_SPROP_FOUNDATION`, all with zero statement-only
dependencies, semantic premises, self-dependencies, and unexpected axioms.
The remaining three are `minimal_superadditive_extension` and its two
dependent theorems. **Whole-file publication has not happened; cumulative
accepted coverage remains 269/2439 declarations and 30/357 files.**

## 2026-09-23 20:46:24 +08:00 — recursive/list extension definition certified

The validation-only Lean computation interface compiled with `rfl` guards
for the actual production extension body and the actual `index_iota`, `max0`,
`range'`, `map`, and `foldl` operations. Its 105,711-byte export imported
successfully as 166 entries; all earlier nine certificates were rebuilt
against this exact new imported snapshot rather than reusing stale `.vo`.
The source side uses byte-identical pinned definitions for `util/list.v:max0`
and `util/superadditivity.v:minimal_superadditive_extension`.

`sa_minimal_extension_related` now kernel-proves the full computational
correspondence: truncated subtraction, ordered `index_iota` enumeration,
list mapping, Nat maximum fold, and the final production definition are
composed from separately proved operation lemmas. A cross-artifact shortcut
for the existing Nat subtraction adapter **failed definitional equality**;
the current artifact therefore has a small independently proved subtraction
adapter, not a silent assumption. Automatic audit reports **10/10** completed
declarations with no semantic premise, statement-only dependency,
self-dependency, or unexpected assumption. Two dependent horizon theorems
remain. Their source extraction initially failed because an open Section
hypothesis referred to the pre-closure implicit parameter form; the extractor
now explicitly omits that obsolete context *only when using the previously
recorded exact post-Section elaborated theorem type*, with the transformation
recorded in metadata. The resulting source statement slices compile.

Project accepted coverage is still **269/2439**, since no 12/12 whole-file
publication has occurred.

## 2026-09-23 20:52:26 +08:00 — update-operation bridge compiled

The validation-only computation interface was extended with `updateValue`,
`updateValueEq`, and `updateValueNe` guards for the actual production
conditional expression. Its latest export imports 207 declarations; all ten
existing certificates were recompiled against that artifact rather than
silently reusing the previous 166-entry import. The new Rocq
`sa_update_related` proof now compiles for both `t = h` and `t ≠ h`, composing
the certified minimal-extension bridge with the imported equality decision.
The first attempt failed when dependent elimination substituted away `hL`,
and the second exposed an SProp/Type elaboration issue for the negative case;
both were local proof-construction errors, not semantic counterexamples.
This operation bridge is not itself one of the twelve public declarations.
The two remaining horizon theorem statement certificates and a fresh
assumption audit of the 207-entry snapshot are still pending; formal coverage
remains **269/2439 declarations, 30/357 files**.

## 2026-09-23 21:00:40 +08:00 — all twelve correspondence proofs pass; audit issue resolved

Both remaining horizon theorem *statement* certificates compile by composing
the independently proved update-value operation relation, the existing
`superadditive_until`/`superadditive_at` correspondences, and the Nat successor
bridge. Neither source nor imported target theorem proof is used. Rocq
exact-type guards also accepted both compiled Lean theorem types.

The first full 12-target `Print Assumptions` audit rejected the two new
certificates: validation-only `updateValueEq/Ne` helper proofs used `simp`,
which pulled in imported Lean `propext`. This was an actual fail-closed audit
finding, not a translation mismatch. Replacing those helper proofs with
direct `decide_eq_true`/`decide_eq_false` rewrites made Lean `#print axioms`
report *no axioms* for either helper. After fresh fixture compilation,
export (`SHA-256 7448ff2f3a0abd9ff0013c950679234f3636c7955540420f5f7c20817826827a`,
113,567 bytes), import (176 entries), and recompilation of every certificate,
the automatic audit passes **12/12** with `semantic_premises = []`,
`statement_only_dependencies = []`, no source/target theorem self-dependency,
and no unexpected assumptions. The sole non-kernel theorem-level bridge remains
the explicitly labeled Prop/SProp `interpret_strict`, alongside importer
foundation/UIP assumptions. Whole-file baseline/provenance publication is
still pending; published accepted coverage remains **269/2439, 30/357**.

## 2026-09-23 21:05:24 +08:00 — pre-publication checks passed

A single combined source slice now auto-extracts all **12/12** declarations
from the pinned official file. Computational blocks remain byte-identical;
theorem statements use the recorded post-Section elaborated types. The
source-compatibility replacements (`util.rel` and the already extracted
`max0`) and omission of obsolete open Section context are explicit in the
metadata. This combined source module compiles in Rocq 9.3. The production
Lean module and its six required utility modules have a sealed isolated
`CLEAN_FULL` build manifest; the updated computation fixture was freshly
compiled. Lean's twelve-declaration proof-axiom classifier passes with only
the exact allowed standard axioms on theorem proofs. The frozen-baseline
audit is `PASS`, and the 12/12 semantic assumption audit remains `PASS`.
Publication/configuration is the only remaining step before increasing formal
coverage.

## 2026-09-23 21:08:53 +08:00 — whole-file accepted

The combined official-source extraction, its six proof-facing source slices,
and all twelve source-binding conversion guards compiled. The target's twelve
Lean type freezes and proof-axiom checks passed, as did the two horizon exact
target-type guards. The current export/import is the 176-entry, 113,567-byte
artifact identified above. All twelve certificate sections passed the
fail-closed assumption audit with no semantic premises, theorem
self-dependencies, statement-only dependencies, or unexpected axioms. The
baseline/invalidation audit and the snapshot-aware whole-file publisher also
passed. Published evidence is under
`Validation/imported/translation_order/superadditivity/`; the machine state is
`Validation/planning/v06_pipeline/util_superadditivity_module_{manifest,status}.json`.

**Final file status:** `ACCEPTED_V06_FILE`, 12/12 declarations, all labeled
`CERTIFIED_WITH_PROP_SPROP_FOUNDATION` (not axiom-free). Formal cumulative
coverage is now **281/2439 declarations, 31/357 files**;
translated-but-not-certified remains **0**. The previous blocked
`util/lcmseq.v` file remains separate and is not counted as accepted.
