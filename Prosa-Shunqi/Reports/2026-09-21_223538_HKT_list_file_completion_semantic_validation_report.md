# `util/list.v` Completion and Whole-File Semantic Validation

Start time: **2026-09-21 22:35:38 HKT**

Authority: Prosa v0.6 commit
`414e66760333eaa4ef78c685bcf53291c527a548`; Lean 4.33.1; Mathlib
`0df444a360eaa60ab8c11dca51a86af692955474`; Rocq 9.3.

Scope is restricted to the final nine declarations of `util/list.v` and the
subsequent unified regression of all 57 declarations. `util/sum.v` and
`Prosa-fei/` remain out of scope.

## 2026-09-21 22:35:38 HKT — Contracts confirmed and Lean candidates compiled

The authoritative inventory confirms exactly nine remaining declarations, in
source order:

1. `index_iota_filter_step`
2. `range_iota_filter_step`
3. `iota_filter_gt`
4. `sub_count_seq`
5. `count_predUI'`
6. `prefix_of`
7. `strict_prefix_of`
8. `shift_points_pos`
9. `shift_points_neg`

The first three are v0.6 signature evolutions with a high-provenance v0.4
implementation strategy; the remaining six are `NEW_IN_V06`. All nine were
translated from the v0.6 contracts in one production edit. The approved
representations are preserved: sequence order/multiplicity use `List`, source
Boolean predicates remain `Bool`, natural subtraction remains truncated, and
the `eqType` boundary of both prefix definitions explicitly carries
`DecidableEq`.

`lake env lean Prosa/Util/List.lean` passes for all 57 declarations. No
semantic acceptance is claimed at this milestone; proof/axiom audit,
fresh export/import, independent correspondence certificates, and the
whole-file regression remain pending.

## 2026-09-21 22:44:40 HKT — Full List snapshot prepared

- Lean proof/axiom audit for the final nine candidates: **9 / 9 PASS**.
  The four definitions are axiom-free; the five theorem proofs use only the
  current explicit allowlist (`propext`, and where present `Quot.sound`).
- Fixed two syntax-boundary issues exposed by the final declaration names:
  source extraction now handles Rocq identifiers ending in `'`, and the Lean
  axiom parser now handles quoted Lean names containing `'`. These changes do
  not alter translation or semantic policy.
- Source acquisition covers all 57 public declarations: 56 in the main
  source slice plus `first0` in the established simple-definition slice.
  The final five theorem types come from elaborated Rocq `Check` evidence;
  the final four definition blocks are byte-exact from the pinned source.
- Frozen snapshot:
  `59d6a91640446026d494ea4a2f647bbcbdf3283aa97deded47e74351225308ff`.
- One successful fresh prepare completed:

| Stage | Executions | Mode | Time |
|---|---:|---|---:|
| Lean build | 1 | `FRESH` | 19.343 s |
| source acquisition | 1 | `FRESH` | 3.445 s |
| lean4export | 1 | `FRESH` | 2.529 s |
| rocq-lean-import | 1 | `FRESH` | 35.026 s |

The first prepare attempt failed closed before publication because the type
probe guessed an encoded name for Lean's trailing apostrophe; the importer
actually preserves the Rocq-valid apostrophe. The probe was corrected and the
successful snapshot above was rebuilt fresh. All subsequent certificate-only
work must reuse this snapshot by verified hashes.

## 2026-09-21 23:00:19 HKT — Final-cluster operation layer compiled

The imported artifact exposed an important representation detail: the
universe-polymorphic imported `List.map` and the Nat-specialized
`List_map_inst3` used by the production shift definitions are distinct
imported objects. The generic computation theorem therefore could not be
used as evidence for the specialized production operation. A validation-only
Lean interface now exports kernel-checked equations for that exact
Nat-specialized operation. This computation-interface change correctly
invalidated the previous preparation cache.

A replacement frozen snapshot was built fresh:
`014a943a98477db29473336b601d78c32e7d00bf3a71c67831162a91cec6d208`.
Its measured preparation stages were: Lean build 26.819 s, source acquisition
3.884 s, export 2.496 s, and Rocq import 36.571 s (69.770 s total).

`ListBatch5Operations.v` now compiles against that actual artifact. It adds
two reusable, independently proved operation correspondences:

- ordered Nat `map` preservation for related functions and lists;
- generic MathComp `count` ↔ actual imported Lean `List.countP`, proved by
  list induction from imported computation equations and existing Bool/Nat
  bridges.

The subsequent certificate-only check hit the verified preparation cache and
did not execute Lean build, export, or import. The nine target-level
certificates and unified 57-target finalization remain pending at this
milestone.

## 2026-09-21 23:19:35 HKT — All nine semantic certificates compiled

The final imported computation interface also required a distinct
Nat-specialized `countP` equation: the theorem `count_predUI'` refers to
`List_countP_inst1`, while generic `sub_count_seq` refers to polymorphic
`List_countP`. Both actual imported operations now have separate certified
bridges. The resulting current frozen snapshot is
`2c13e147b6cc0bfd6e40b4216b57336a45c0fdb615e29a6c123de914e2941ac6`.

All nine independent correspondence certificates now compile in Rocq 9.3,
and the fail-closed automatic `Print Assumptions` audit reports:

- `shift_points_pos`: `CERTIFIED`;
- the other eight targets: `CERTIFIED_WITH_PROP_SPROP_FOUNDATION`;
- semantic premises: none;
- source theorem dependencies: false;
- target theorem dependencies: false;
- unexpected assumptions: none.

The three newly reusable operation certificates (`map`, polymorphic
`countP`, and Nat-specialized `countP`) are each `CERTIFIED` without the
Prop/SProp foundation. The successful certificate-only run reused the
prepared snapshot by verified hash: Lean build/export/import executions were
zero for that run; certificate compilation took 17.969 s and audit took
0.038 s. Exact target-type guards also compiled. Unified 57-target finalize
and publication remain pending, so the accepted baseline is deliberately not
updated yet.

## 2026-09-21 23:27:02 HKT — Whole-file finalize passed; `util/list.v` is 57/57 accepted

The unified finalize regression for the current snapshot completed
successfully. It rebuilt all certificate modules in a fresh Rocq work
directory, reran the combined Lean and Rocq assumption audits, checked the
frozen baselines and provenance bindings, and published evidence only after
all gates passed.

The final nine declarations have these machine-derived statuses:

| Declaration | Semantic status | Acceptance |
|---|---|---|
| `index_iota_filter_step` | `CERTIFIED_WITH_PROP_SPROP_FOUNDATION` | `ACCEPTED_V06_TRANSLATION` |
| `range_iota_filter_step` | `CERTIFIED_WITH_PROP_SPROP_FOUNDATION` | `ACCEPTED_V06_TRANSLATION` |
| `iota_filter_gt` | `CERTIFIED_WITH_PROP_SPROP_FOUNDATION` | `ACCEPTED_V06_TRANSLATION` |
| `sub_count_seq` | `CERTIFIED_WITH_PROP_SPROP_FOUNDATION` | `ACCEPTED_V06_TRANSLATION` |
| `count_predUI'` | `CERTIFIED_WITH_PROP_SPROP_FOUNDATION` | `ACCEPTED_V06_TRANSLATION` |
| `prefix_of` | `CERTIFIED_WITH_PROP_SPROP_FOUNDATION` | `ACCEPTED_V06_TRANSLATION` |
| `strict_prefix_of` | `CERTIFIED_WITH_PROP_SPROP_FOUNDATION` | `ACCEPTED_V06_TRANSLATION` |
| `shift_points_pos` | `CERTIFIED` | `ACCEPTED_V06_TRANSLATION` |
| `shift_points_neg` | `CERTIFIED_WITH_PROP_SPROP_FOUNDATION` | `ACCEPTED_V06_TRANSLATION` |

For every one of the nine certificates, the automatic audit reports no
semantic premise, no source-theorem dependency, no target-theorem dependency,
and no unexpected assumption. The operation layer added three independently
proved and reusable certificates: ordered Nat `map`, polymorphic `countP`, and
Nat-specialized `countP`. None of those operation certificates depends on the
Prop/SProp foundation.

Across the complete `util/list.v` inventory, the published manifest now
contains exactly 57 distinct source declarations: 5 are `CERTIFIED`, 52 are
`CERTIFIED_WITH_PROP_SPROP_FOUNDATION`, and all 57 are
`ACCEPTED_V06_TRANSLATION`. Thus:

```text
util/list.v = ACCEPTED_V06_FILE
List accepted = 57 / 57
List remaining = 0
```

The final content-addressed snapshot is:

```text
2c13e147b6cc0bfd6e40b4216b57336a45c0fdb615e29a6c123de914e2941ac6
```

Its one fresh preparation executed:

| Stage | Executions | Mode | Time |
|---|---:|---|---:|
| Lean build | 1 | `FRESH` | 18.739086 s |
| source acquisition | 1 | `FRESH` | 3.278109 s |
| lean4export | 1 | `FRESH` | 2.194297 s |
| rocq-lean-import | 1 | `FRESH` | 35.773852 s |
| **Preparation total** | **4** | `FRESH` | **59.985344 s** |

The successful whole-file finalize verified the same prepared artifacts by
hash and therefore executed no duplicate Lean build, source acquisition,
export, or import. It recorded four `VERIFIED_CACHE` hits, then ran:

| Stage | Executions | Mode | Time |
|---|---:|---|---:|
| certificate compile | 1 | `FRESH` | 30.997407 s |
| assumption/provenance audit | 1 | `FRESH` | 13.132838 s |
| publication | 1 | `FRESH` | 1.146863 s |
| **Finalize total** | **3** | `FINALIZE_VERIFIED_CACHE` | **45.296225 s** |

An earlier finalize reached publication and failed closed because the Batch 5
cluster metadata incorrectly listed a cluster-local operation certificate as
a common-library bridge. No certificate or semantic result failed. The
metadata was corrected, and the complete finalize was rerun rather than
partially resumed.

The cumulative machine state after publication is:

```text
accepted files                 = 11 / 357
accepted declarations          = 106 / 2439
translated-but-not-certified   = 0
deferred external boundary     = 239
```

`util/sum.v` remains unchanged at 3/25 accepted; its remaining 22 declarations
keep the overall utility-expansion status `PARTIAL`. The frozen prior
baselines, pinned source, mapping/dependency snapshots, and historical
`Prosa-fei` tree passed the baseline audit. `git diff --check` passed. Old
`.lia.cache` files under ignored temporary run directories were removed; the
workspace ignore rules already cover them.
