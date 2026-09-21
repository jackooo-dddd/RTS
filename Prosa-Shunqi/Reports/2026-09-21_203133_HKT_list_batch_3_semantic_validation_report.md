# List Batch 3 Semantic Validation

Start time: **2026-09-21 20:31:33 HKT**

Scope is limited to the following nine declarations from pinned Prosa v0.6
`util/list.v`, in authoritative source order:

1. `subseq_leq_size`
2. `in_zip`
3. `eq_ind_in_seq`
4. `default_or_in`
5. `exists_two`
6. `has_all_nilp`
7. `sorted_split`
8. `sorted_cat`
9. `nonnil_last`

`util/sum.v` is outside this run and remains unchanged.

## 2026-09-21 20:31:33 HKT — Lean translation snapshot frozen

- Read and applied `.agents/skills/prosa-v06-translation/SKILL.md`.
- Confirmed all nine declarations and their elaborated source types against the
  workspace-local pinned Prosa v0.6 checkout at commit
  `414e66760333eaa4ef78c685bcf53291c527a548`.
- Added all nine Lean declarations to `Prosa/Util/List.lean` in source order.
- Added one validation-relevant Lean helper, `boolSorted`, representing the
  MathComp adjacent Boolean `sorted` observation as `List.IsChain` over
  `R x y = true`.
- `lake env lean Prosa/Util/List.lean`: **PASS**.
- Independent `#print axioms` results for all nine contain only the existing
  project-allowed Lean foundations (`propext`, and where used
  `Classical.choice` / `Quot.sound`); no `sorryAx` or custom axiom occurred.
- Added validation-only computation equations needed for generic `getD`,
  `zip`, `idxOf`, `all`, `any`, `isEmpty`, `getLastD`, and `boolSorted`.
  The fixture compiles against a fresh isolated `List.olean`.
- `git diff --check`: **PASS**.

The production and computation-interface inputs are now frozen for one shared
prepare run. No semantic certificate is claimed at this stage.

Current machine-checked status:

| Declaration | Lean compile | Lean proof audit | Semantic certificate |
|---|---:|---:|---:|
| all nine targets | PASS | PASS | NOT_YET_VALIDATED |

Baseline before this snapshot: List `30 / 57`, project `79 / 2439`, and zero
translated-but-uncertified declarations. Those historical certificates are
now stale until the final unified regression binds them to this snapshot.

## 2026-09-21 21:07:00 HKT — Shared prepare complete; operation DAG compiles

- Ran `./Validation/scripts/prepare_utility_list_batch.sh` exactly once for
  snapshot
  `4446f1dfbd8e00641c188d6e0ac15a039b04490fda3c78e63971522e6a2b8f0a`.
- The shared prepare was `FRESH`: Lean build `17.991457 s`, source acquisition
  `3.393432 s`, export `2.443544 s`, Rocq import `36.153370 s`; total
  `59.981803 s`.  This produced the actual imported theorem types and
  computation interfaces used below.
- All subsequent work in this phase was certificate-only against that exact
  prepared artifact.  Lean build/export/import execution count remained
  `1 / 1 / 1` for the snapshot.
- `ListBatch3Operations.v` now compiles in Rocq against the prepared artifact.
  It reuses the certified Nat, equality/DecidableEq, seq/List, membership,
  length, append, filter, Bool/reflection, and Prop/SProp layers, and adds the
  smallest missing operations for this target group:
  `uniq <-> List.Nodup`, generic `getD`, `all`/`any`/`isEmpty`, generic
  `getLastD`, Nat-valued functions and decided order, Boolean sortedness,
  source-pair/imported-Prod list+membership, `zip`, and `index/idxOf`.
- `Print Assumptions` on these bridges reports only the existing audited
  importer/kernel foundations and, for reverse SProp-to-Prop paths, the sole
  approved `PropSPropFoundation.interpret_strict`.  No new axiom or semantic
  premise was introduced.

No target theorem is marked certified yet: the next stage composes these
operation certificates into nine independent theorem-statement
correspondences and audits target/source self-dependency.

## 2026-09-21 21:20:06 HKT — Nine correspondence proofs and exact-type guards pass

- `ListBatch3Certificate.v` compiles against the frozen imported artifact and
  contains an independent structural correspondence proof for each of the
  nine targets.  None of these proofs invokes the official source theorem
  proof constant or the imported Lean target theorem constant.
- `ListBatch3TypeAudit.v` compiles: all nine structural target propositions
  type-check against the exact theorem constants exported from the actual
  compiled Lean snapshot after specialization at the approved
  `eqType -> Type + DecidableEq` boundary.
- The marked `Print Assumptions` probe and fail-closed classifier pass for all
  nine certificates.  For every target:
  `semantic_premises = []`, source theorem dependency is `false`, target
  theorem dependency is `false`, and `unexpected = []`.
- Every proof currently uses the single approved reverse
  SProp-to-Prop boundary `PropSPropFoundation.interpret_strict`, so the
  provisional semantic status of all nine is
  `CERTIFIED_WITH_PROP_SPROP_FOUNDATION`, not plain `CERTIFIED`.

These are machine-checked intermediate results.  Publication remains pending
the snapshot-aware check and the unified regression of the previous 30 plus
the new nine declarations.

## 2026-09-21 21:22:59 HKT — Incremental check passes without rebuilding Lean

- Ran `check_utility_list_batch.sh` against snapshot `4446f1dfbd8e...`.
- The prepared-artifact verifier reported four `VERIFIED_CACHE` hits and zero
  executions for Lean build, source acquisition, Lean export, and Rocq import.
  Hash verification of those four stages took `0.010443 s` total.
- Only the affected Rocq certificate DAG was compiled (`7.361586 s`) and its
  assumptions classified (`0.033801 s`).
- The fail-closed audit classified all nine targets as
  `CERTIFIED_WITH_PROP_SPROP_FOUNDATION`, with no semantic premises, no
  theorem self-dependencies, and no unexpected assumptions.

This confirms that certificate-only work did not repeat the expensive
Lean/export/import preparation.  Formal publication still awaits the unified
39-declaration finalize regression.

## 2026-09-21 21:24:15 HKT — Unified regression and publication pass

`finalize_utility_list_batch.sh` completed successfully for the same snapshot
`4446f1dfbd8e00641c188d6e0ac15a039b04490fda3c78e63971522e6a2b8f0a`.
It recompiled and audited the complete correspondence certificate set for the
previous 30 and the new nine List targets, then published only evidence bound
to that current snapshot.

| New declaration | Final semantic status | Acceptance |
|---|---|---|
| `subseq_leq_size` | `CERTIFIED_WITH_PROP_SPROP_FOUNDATION` | `ACCEPTED_V06_TRANSLATION` |
| `in_zip` | `CERTIFIED_WITH_PROP_SPROP_FOUNDATION` | `ACCEPTED_V06_TRANSLATION` |
| `eq_ind_in_seq` | `CERTIFIED_WITH_PROP_SPROP_FOUNDATION` | `ACCEPTED_V06_TRANSLATION` |
| `default_or_in` | `CERTIFIED_WITH_PROP_SPROP_FOUNDATION` | `ACCEPTED_V06_TRANSLATION` |
| `exists_two` | `CERTIFIED_WITH_PROP_SPROP_FOUNDATION` | `ACCEPTED_V06_TRANSLATION` |
| `has_all_nilp` | `CERTIFIED_WITH_PROP_SPROP_FOUNDATION` | `ACCEPTED_V06_TRANSLATION` |
| `sorted_split` | `CERTIFIED_WITH_PROP_SPROP_FOUNDATION` | `ACCEPTED_V06_TRANSLATION` |
| `sorted_cat` | `CERTIFIED_WITH_PROP_SPROP_FOUNDATION` | `ACCEPTED_V06_TRANSLATION` |
| `nonnil_last` | `CERTIFIED_WITH_PROP_SPROP_FOUNDATION` | `ACCEPTED_V06_TRANSLATION` |

Final gates:

- Current-snapshot publication coverage: `3 + 27 + 9 = 39` List declarations.
- Combined Lean axiom audit: 42 configured proof/definition entries, no
  missing or extra output, no forbidden axiom.
- Combined Rocq assumption audit: 39 certificates total; 3 `CERTIFIED` and 36
  `CERTIFIED_WITH_PROP_SPROP_FOUNDATION`; no conditional result, unexpected
  assumption, source theorem dependency, or target theorem dependency.
- Baseline audit before and after regression: `PASS`.
- `git diff --check`: `PASS`.
- Production scan found no `sorry`, custom `axiom`, or `unsafe` escape.

### Reused and new correspondence layers

Reused certified dependencies included Nat and order, `eqType`/`DecidableEq`,
ordered `seq`/`List`, membership, length, append, filter, Boolean reflection,
equality, conjunction/implication/existential transport, and the approved
Prop/SProp foundation.

The new target-driven operation layer adds the reusable correspondences needed
by this cluster: `uniq`/`List.Nodup`, generic defaulted indexing, `all`/`any`,
`nilp`/`isEmpty`, generic `last`/`getLastD`, Nat-valued functions and decided
order, binary Boolean predicates, adjacent `sorted`/`List.IsChain`, source
pairs/imported `Prod`, pair-list membership, `zip`, and `index`/`idxOf`.
No unresolved operation correspondence remains for these nine targets.

### Instrumented execution and timing

Across the official prepare/check/finalize path for this frozen snapshot:

- Lean build executions: **1** (`17.991457 s`).
- Source acquisition executions: **1** (`3.393432 s`).
- Lean export executions: **1** (`2.443544 s`).
- Rocq import executions: **1** (`36.153370 s`).
- Incremental check: four verified prepare cache hits; affected certificate
  compile `7.361586 s`, audit `0.033801 s`.
- Finalize: four verified prepare cache hits; full certificate regression
  `20.233647 s`, audit `10.654384 s`, publication `0.736401 s`.
- Total verified prepare cache hits after the fresh prepare: **8**.

The development proof probes that preceded the instrumented check are not
misreported as pipeline stage executions; the figures above come directly
from the recorded stage-evidence JSON files.

### Published state

- List: **39 / 57 accepted**, 18 remaining.
- Project: **88 / 2439 accepted declarations**.
- Project accepted files: **10 / 357**.
- Translated but not certified: **0**.

The List source file remains a partial file because 18 authoritative
declarations are outside this batch; that does not affect acceptance of the
39 declaration-level results above.

## 2026-09-21 21:25:46 HKT — Completion verdict

All final machine-state assertions passed, `Prosa-fei/` has no working-tree
change from this batch, and the pinned source/planning baseline audits remain
clean.

```text
LIST_BATCH_3_STATUS = PASS
NEW_DECLARATIONS_ACCEPTED = 9 / 9
LIST_ACCEPTED = 39 / 57
PROJECT_ACCEPTED = 88 / 2439
TRANSLATED_BUT_NOT_CERTIFIED = 0
```
