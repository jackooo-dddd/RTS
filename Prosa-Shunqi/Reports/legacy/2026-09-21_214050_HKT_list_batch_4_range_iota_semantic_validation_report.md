# List Batch 4 — Range/Iota Semantic Validation

Start time: **2026-09-21 21:40:50 HKT**

Scope is restricted to nine declarations from pinned Prosa v0.6
`util/list.v`, commit `414e66760333eaa4ef78c685bcf53291c527a548`,
in source order:

1. `filter_last_mem`
2. `range`
3. `iotaD_impl`
4. `index_iota_lt_step`
5. `index_iota_cat`
6. `range_filter_2cons`
7. `index_iota_filter_eqx`
8. `index_iota_filter_singl`
9. `index_iota_filter_inxs`

`util/sum.v` and `Prosa-fei/` are outside this batch.

## 2026-09-21 21:40:50 HKT — Authority and declaration contracts confirmed

- Latest machine state confirms List `39 / 57`, project `88 / 2439`, and
  translated-but-not-certified `0`.
- Workspace pins are intact: Lean `4.33.1`, Mathlib
  `0df444a360eaa60ab8c11dca51a86af692955474`, Rocq `9.3+rc1`, and the clean
  workspace-local source checkout at the authoritative commit/tree.
- Read and applied `.agents/skills/prosa-v06-translation/SKILL.md`, including
  its correspondence-dependency-DAG and actual-computation-interface rules.
- The elaborated source evidence gives the following exact contracts:

| Declaration | Elaborated source contract summary |
|---|---|
| `filter_last_mem` | for `X : eqType`, `has P xs -> last d (filter P xs) \in xs` |
| `range` | `nat -> nat -> seq nat`; body `index_iota a b.+1` |
| `iotaD_impl` | split `iota m n` at any `n_le <= n` |
| `index_iota_lt_step` | for `a < b`, expose head `a` and successor interval |
| `index_iota_cat` | split the half-open index interval at `t` under `t1 <= t <= t2` |
| `range_filter_2cons` | duplicate list-membership head does not affect filtered range |
| `index_iota_filter_eqx` | equality-filtered `[a,b)` is singleton `[x]` when `a <= x < b` |
| `index_iota_filter_singl` | singleton-membership filter has the same result |
| `index_iota_filter_inxs` | removing an element below interval start preserves the membership filter |

The source `index_iota` used by these contracts is MathComp's external
definition `iota m (n - m)`.  It is not an additional Prosa public target;
the Lean side therefore needs an explicitly marked helper with the same
half-open ordered-list semantics.  No semantic result is claimed yet.

## 2026-09-21 21:49:53 HKT — Nine Lean candidates complete; snapshot frozen

- Added the nine declarations to `Prosa/Util/List.lean` without touching Sum
  or the historical workspace.
- Added one explicitly marked Lean helper, `index_iota`, representing the
  external MathComp operation as `List.range' a (b - a)`; production `range`
  is `index_iota a (b + 1)`, preserving order, multiplicity, and endpoints.
- `lake env lean Prosa/Util/List.lean`: **PASS** for all nine proofs.
- Fail-closed Lean axiom audit: **9 / 9 PASS**.  `range` is axiom-free; the
  eight theorem proofs use only the currently allowed `propext` and
  `Quot.sound`.  There is no `sorryAx`, custom axiom, or unsafe escape.
- Added validation-only, kernel-checked computation equations for actual
  `List.range'`, production `index_iota`, and production `range`.
- The production source and computation interface are now frozen for a single
  shared fresh prepare.  Certificate work after prepare must not change them.

## 2026-09-21 21:50:19 HKT — One shared fresh prepare completed

- Frozen snapshot: `bd4a19f04c48889598397e144796c65d83a51be38153225ee254c066b8d1044c`.
- The actual compiled artifact contains the production bodies of `index_iota`
  and `range`, the exact compiled types of all eight theorem targets, and the
  validation-only `rfl` computation equations for `List.range'`.
- Stage executions and measured wall time:

| Stage | Executions | Mode | Time |
|---|---:|---|---:|
| Lean build | 1 | `FRESH` | 22.576 s |
| source acquisition | 1 | `FRESH` | 3.356 s |
| lean4export | 1 | `FRESH` | 3.938 s |
| rocq-lean-import | 1 | `FRESH` | 35.102 s |

No certificate-only edit after this point has rebuilt or re-exported Lean.

## 2026-09-21 22:11:14 HKT — Eight independent correspondences compile

- Added `ListBatch4Operations.v`.  The Rocq kernel now checks reusable
  operation correspondences for MathComp `iota` versus actual imported
  `List.range'`, MathComp `index_iota` versus production `index_iota`, the
  inclusive Prosa `range`, truncated Nat subtraction, and Nat equality/list
  membership Boolean observations used by filters.
- Added `ListBatch4Certificate.v`.  The following eight semantic
  correspondence proofs compile without a semantic premise and without using
  either source or target theorem constants as their own proof:

  `filter_last_mem`, `range`, `iotaD_impl`, `index_iota_lt_step`,
  `index_iota_cat`, `range_filter_2cons`, `index_iota_filter_eqx`, and
  `index_iota_filter_singl`.
- Added `ListBatch4TypeAudit.v`.  Kernel elaboration accepts all seven theorem
  target guards in this subset against their exact freshly imported compiled
  types; `range_definition_certificate` directly mentions the imported
  production `range` constant and its body correspondence.
- These are machine-compiled intermediate results, not yet published
  acceptance.  Assumption classification and the unified 48-target finalize
  remain pending.
- Remaining target: `index_iota_filter_inxs`.  Its Nat-specialized actual
  `rem_all` is exported through `List.brecOn`; the already-certified generic
  `rem_all` bridge is not definitionally interchangeable with this separately
  imported monomorphic List carrier.  A minimal specialized computation
  interface is still required; no equality premise or axiom has been added.

## 2026-09-21 22:20:14 HKT — All nine certificates pass fail-closed audit

- Closed the final `index_iota_filter_inxs` obligation with a minimal
  Nat-specialized correspondence for the **actual imported** `rem_all` body.
  Its nil/cons equations are checked by imported definitional equality; no
  hand-written target model, extra export, semantic premise, or axiom was
  introduced.
- Removed an unnecessary cross-artifact dependency on `ImportedNat`: the
  truncated-subtraction computation lemma is now local to the actual
  `ImportedListLast` Nat body.
- `ListBatch4Operations.v`, `ListBatch4Certificate.v`,
  `ListBatch4TypeAudit.v`, and `ListBatch4AssumptionAudit.v` all compile.
- Automatic `Print Assumptions` classification gives:

| Declaration | Status |
|---|---|
| `filter_last_mem` | `CERTIFIED_WITH_PROP_SPROP_FOUNDATION` |
| `range` | `CERTIFIED` |
| `iotaD_impl` | `CERTIFIED_WITH_PROP_SPROP_FOUNDATION` |
| `index_iota_lt_step` | `CERTIFIED_WITH_PROP_SPROP_FOUNDATION` |
| `index_iota_cat` | `CERTIFIED_WITH_PROP_SPROP_FOUNDATION` |
| `range_filter_2cons` | `CERTIFIED_WITH_PROP_SPROP_FOUNDATION` |
| `index_iota_filter_eqx` | `CERTIFIED_WITH_PROP_SPROP_FOUNDATION` |
| `index_iota_filter_singl` | `CERTIFIED_WITH_PROP_SPROP_FOUNDATION` |
| `index_iota_filter_inxs` | `CERTIFIED_WITH_PROP_SPROP_FOUNDATION` |

For every row: `semantic_premises=[]`, source theorem dependency is false,
target theorem dependency is false, and unexpected assumptions are empty.
The only theorem-level trust boundary is the approved
`PropSPropFoundation.interpret_strict`; `range` does not use it.

The incremental `check` reused all four prepared stages by verified hash:
Lean build, source acquisition, export, and Rocq import each had zero new
executions.  Fresh certificate compilation took 12.690 seconds and the
fail-closed audit took 0.035 seconds.

## 2026-09-21 22:24:22 HKT — Unified 48-target finalize passed

- The first two finalize attempts stopped in publication, not semantics:
  the partial-cluster publisher initially rejected newer source metadata as a
  strict superset, then a config treated an operation certificate as a common
  bridge path.  The publisher now permits a partial cluster's metadata to be
  a superset only when every extra name belongs to the official inventory;
  missing required declarations and unknown declarations still fail closed.
  Operation-certificate source/VO hashes are recorded as separate additional
  evidence.
- Final regression compiled and audited all previous 39 certificates plus the
  nine new certificates: **48 / 57 ACCEPTED**.
- Successful-finalize timings:

| Stage | Executions | Mode | Time |
|---|---:|---|---:|
| Lean build | 0 | `VERIFIED_CACHE` | 0.005 s |
| source acquisition | 0 | `VERIFIED_CACHE` | 0.002 s |
| lean4export | 0 | `VERIFIED_CACHE` | 0.002 s |
| rocq-lean-import | 0 | `VERIFIED_CACHE` | 0.003 s |
| certificate compile (48-target regression) | 1 | `FRESH` | 25.158 s |
| Lean/Rocq/baseline audit | 1 | `FRESH` | 12.720 s |
| publication | 1 | `FRESH` | 0.949 s |

Across the frozen Batch-4 snapshot, expensive preparation executed exactly
once: Lean build `1`, source acquisition `1`, export `1`, and import `1`.
The later official check plus three finalize attempts produced 16 verified
prepare-stage cache hits and no additional Lean build/export/import.  The two
failed finalize attempts are retained in raw logs as publication-debugging
evidence.

## 2026-09-21 22:25:59 HKT — Published state

- New accepted declarations: **9 / 9**.
- List cumulative: **48 / 57 accepted**, **9 remaining**.
- Project cumulative: **97 / 2439 accepted**.
- Translated-but-not-certified: **0**.
- New reusable operation correspondences: actual `List.range'`/MathComp
  `iota`, production `index_iota`, inclusive `range`, local truncated Nat
  subtraction, Nat equality-as-Bool, Nat membership-as-Bool, and the
  Nat-specialized actual imported `rem_all` interface.
- Reused certified correspondence families: Nat/order/equality, seq/List,
  membership, append, filter, last/getLastD, any, Boolean reflection,
  list equality, and the approved Prop/SProp foundation.
- `util/sum.v` and `Prosa-fei/` remained unchanged.
- `git diff --check`: **PASS**.
