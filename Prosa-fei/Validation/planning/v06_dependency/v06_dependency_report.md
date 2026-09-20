# Prosa v0.6 Source Inventory and Dependency Planning Report

## Progress log

### 2026-09-20 18:00 HKT — scope fixed and environment inspection started

- Authoritative source is fixed to official Prosa commit
  `414e66760333eaa4ef78c685bcf53291c527a548` (v0.6).
- Current RTS repository commit is
  `1e18e33c891dc529896bde2c01670d674ae60ade`.
- Frozen `Prosa-fei/Prosa` Git tree object is
  `7426e874bd049e6f007b2695ef13f7209a0a1f8f`.
- The Prosa-specific opam switch reports Rocq `9.0.1` (OCaml `4.14.2`).
- The current global Lean executable reports Lean `4.34.0`, commit
  `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`.
- The validation environment previously pinned Mathlib `v4.33.1`, commit
  `0df444a360eaa60ab8c11dca51a86af692955474`; the generator will verify the
  checkout directly before recording it in the final manifest.
- No production Lean file has been modified. The current work is confined to
  `Validation/planning/v06_dependency/` and validation-only worktrees.

Next: create a detached worktree at the pinned commit, inventory every `.v`
file, and validate file dependencies with Rocq's dependency tool before
constructing declaration-level graphs.

### 2026-09-20 18:12 HKT — exhaustive file extraction and main-library build

- Created a detached validation-only worktree at the exact pinned commit.
- Enumerated **357** `.v` files: 343 in the official main package and 14 under
  `implementation/refinements/`.
- Ran `coqdep -f _CoqProject` over the all-files project. It emitted exactly
  357 file rules. The only reported missing load-path modules are the four
  CoqEAL modules required by the refinement package (`hrel`, `param`,
  `refinements`, and `binnat`). These files remain in every inventory and are
  not silently excluded.
- Successfully compiled all 343 official main-package modules with Rocq 9.0.1,
  producing 343 `.glob` files. This supplies elaborator-generated reference
  locations for statement/body dependency extraction.
- Initial graph construction found 357 nodes, 1,358 internal file edges, 30
  layers, and no file-level strongly connected component with more than one
  node.
- Initial public-declaration extraction found 2,429 source declarations (this
  baseline was later corrected to 2,439 after recognizing attributed named
  instances). Proof
  references are intentionally excluded: theorem edges are taken only from
  references whose `.glob` positions lie in the theorem statement command;
  computational declarations include both type and body references.

Current work: run `Check @qualified_declaration` against the compiled pinned
modules to replace source-only type fingerprints with post-Section-closure,
elaborated Rocq type fingerprints for every buildable declaration. The 14
refinement files are expected to retain an explicit unresolved type-evidence
status until CoqEAL is installed.

### 2026-09-20 18:18:29 HKT — initial elaborated inventory (superseded)

- At this stage **2,190** declarations in the 343 buildable main-package files were
  successfully resolved by fully qualified name and checked with Rocq
  `Check @declaration`; normalized rendered types and SHA-256 fingerprints are
  in `declaration_type_evidence.json` and `declaration_inventory.csv`.
- The other **239** source declarations belong to the 14 refinement files and
  are explicitly marked `UNRESOLVED_EXTERNAL_BUILD_BOUNDARY_COQEAL`; they are
  not presented as elaborated types.
- Every one of the **1,359** final internal file edges is present in Rocq's
  `coqdep` output. Source parsing supplies only the `Require Import` versus
  `Require Export` label; it does not invent file edges.
- This initial declaration graph contained **4,542** direct edges: 3,077 type,
  1,306 body, 91 structure-field, and 68 instance dependencies.
- Neither the file graph nor the extracted declaration graph has a non-trivial
  strongly connected component. The longest file chain has 30 nodes; the
  longest extracted declaration chain has 14 nodes.

## Final result

### Scope and pinned environment

| Item | Recorded value |
|---|---|
| Authoritative Prosa source | v0.6, commit `414e66760333eaa4ef78c685bcf53291c527a548` |
| Current RTS repository at hardened reproduction | `1996f0829f936973299ca8af13d8190a5ffe97df` |
| Frozen current Lean tree | Git tree `7426e874bd049e6f007b2695ef13f7209a0a1f8f` |
| Rocq used for source build | 9.0.1, OCaml 4.14.2, opam switch `prosa-0.6` |
| MathComp | 2.4.0; MathComp-Zify 1.7.0+2.4+9.0 |
| Existing Lean validation environment | Lean 4.33.1 (`819816b2...`), Mathlib v4.33.1 commit `0df444a360eaa60ab8c11dca51a86af692955474` |
| Current shell Lean (also recorded) | Lean 4.34.0 (`293d5d0c...`) |

Lean and Mathlib do not participate in deriving the v0.6 Rocq graph. They are
recorded only to freeze the surrounding repository/tool context.

The complete source inventory contains **357 files exactly once**:

| Scope class | Files | Treatment |
|---|---:|---|
| Core Prosa source | 325 | main package, compiled and fully inventoried |
| Core aggregation modules (`all.v`) | 4 | main package, retained as real `Require Export` nodes |
| Implementation definitions/facts | 13 | main package, compiled and fully inventoried |
| Implementation refinements | 14 | inventoried; declaration elaboration blocked by missing CoqEAL |
| Library example module | 1 | retained; it is built as part of the official library |
| Tests | 0 | none at this commit |
| Generated `.v` sources | 0 | none at this commit |
| Other non-library `.v` files | 0 | none at this commit |

The exhaustive per-file listing, hashes, categories, and build groups are in
`file_inventory.csv`. No `.v` file was silently omitted.

### File graph

The edge convention is always **dependency → dependent**. The 357-node graph
contains **1,359 direct internal edges**:

- 1,257 `REQUIRE_EXPORT` edges;
- 102 `REQUIRE_IMPORT` edges;
- 1,359/1,359 independently present in `coqdep` output.

External boundaries comprise **178 direct require occurrences**, representing
**24 distinct modules** under four roots:

| External root | Require occurrences | Role |
|---|---:|---|
| MathComp | 165 | core mathematical/library boundary |
| Rocq `Stdlib` | 5 | standard-library boundary |
| Hierarchy Builder (`HB`) | 4 | structure/instance boundary |
| CoqEAL | 4 | refinement-only boundary, unavailable in the current switch |

There are **30 file layers**, numbered 0–29. Layer 0 contains precisely the 11
files whose direct requirements are external only:

`behavior/time.v`, `util/bigop.v`, `util/epsilon.v`, `util/int.v`,
`util/notation.v`, `util/rel.v`, `util/seqset.v`, `util/setoid.v`,
`util/subadditivity.v`, `util/supremum.v`, and `util/tactics.v`.

The graph has no cycle. Nevertheless, `file_dag.json` records every SCC and the
condensation graph rather than assuming acyclicity. One graph-derived longest
chain has 30 nodes and begins

```text
util/supremum.v → util/list.v → util/bigcat.v → util/all.v
→ behavior/job.v → behavior/arrival_sequence.v → behavior/schedule.v
→ behavior/service.v → behavior/ready.v → behavior/all.v → ...
→ results/rta/ideal/edf/bounded_nps.v
→ implementation/refinements/EDF/fast_search_space.v
→ implementation/refinements/EDF/refinements.v
```

The full chain is stored in `file_dag.json` and shown in
`file_dag_summary.md`.

### Public declarations and declaration dependencies

The hardened source-level inventory contains **2,439 public declarations**. It excludes
Section variables/hypotheses, local `Let`s, and compiler-generated
constructors/recursors/projections. All 44 source `Class`/`Record`/`Structure`
declarations have their source fields recorded separately.
Anonymous `HB.instance Definition _` commands are treated as generated
Hierarchy Builder implementation artifacts rather than named public source
declarations; their effects remain visible through elaborated types and
instance references. Anonymous Rocq `Instance : ...` commands likewise do not
become named public inventory nodes; the sole `Defined.` case is recorded
separately in the declaration-method audit.

| Source kind | Count |
|---|---:|
| Lemma | 1,158 |
| Definition | 778 |
| Corollary | 149 |
| Theorem | 101 |
| Instance | 105 |
| Fact | 49 |
| Class | 40 |
| Remark | 39 |
| Fixpoint | 8 |
| Inductive | 8 |
| Structure | 2 |
| Record | 2 |

For 2,200 main-package declarations, the final post-elaboration type evidence
comes from Rocq itself (`Check @fully.qualified.name`) after compiling the exact
pinned source. The 239 refinement declarations retain source-command
fingerprints and an explicit unresolved status because their CoqEAL boundary
is absent.

The hardened explicit translation-relevant graph contains **4,628** edges:

| Edge type | Count |
|---|---:|
| `TYPE_DEPENDENCY` | 3,079 |
| `BODY_DEPENDENCY` | 1,329 |
| `STRUCTURE_FIELD_DEPENDENCY` | 91 |
| `INSTANCE_DEPENDENCY` | 129 |

For lemmas/theorems, only `.glob` references located within the final statement
command are included. References in `Proof ... Qed` are absent by design. For
computational/structural declarations, references in both the declared type
and definition body are included. Thus this graph is not a disguised theorem
proof-dependency graph.

The declaration graph has 14 layers and no detected cycle. It verifies explicit
translation-relevant `.glob` references and mapped generated symbols for the
2,200 compiled main declarations; it does **not** claim that absent edges prove
absence of implicit typeclass/canonical/HB dependencies. All 239 refinement
declarations remain `UNRESOLVED_EXTERNAL`; no guessed refinement edge is
inserted.

### Graph-derived foundations and representation risk

The highest file fan-out nodes include `util/tactics.v` (346 transitive
dependents), `util/supremum.v` (340), `util/list.v` and `util/nat.v` (339 each),
and `behavior/time.v` (332). `util/tactics.v` is operationally foundational for
the file build, but it is not a semantic representation choice; declaration
fan-out distinguishes those cases.

The highest-impact semantic declarations are:

| Declaration | Kind | Declaration layer | Transitive dependents |
|---|---|---:|---:|
| `behavior.job.JobType` | Definition | 0 | 1,403 |
| `behavior.time.instant` | Definition | 0 | 1,370 |
| `behavior.job.work` | Definition | 0 | 1,206 |
| `behavior.schedule.ProcessorState` | Class | 1 | 915 |
| `behavior.arrival_sequence.arrivals_at` | Definition | 1 | 779 |
| `model.task.concept.TaskType` | Definition | 0 | 774 |
| `behavior.schedule.service_in` | Definition | 2 | 684 |
| `behavior.service.service_at` | Definition | 5 | 669 |
| `behavior.time.duration` | Definition | 0 | 643 |
| `behavior.job.JobCost` | Class | 1 | 556 |
| `behavior.service.service_during` | Definition | 5 | 553 |
| `behavior.job.JobArrival` | Class | 1 | 535 |
| `behavior.arrival_sequence.arrivals_between` | Definition | 2 | 497 |
| `behavior.service.service` | Definition | 5 | 475 |
| `model.task.concept.JobTask` | Class | 1 | 452 |
| `behavior.schedule.scheduled_in` | Definition | 2 | 397 |
| `behavior.service.scheduled_at` | Definition | 3 | 386 |
| `behavior.service.completed_by` | Definition | 6 | 358 |

Consequently, wrong representations for `JobType`, `instant`, `work`,
`ProcessorState`, or `TaskType` have the widest measured blast radius. The
service chain (`service_in` → `service_at`/`service_during` → `service` and
completion predicates) is the next critical structural boundary. Arrival
sequence representation is likewise high-impact through `arrivals_at` and the
interval aggregators.

MathComp big operators are an external semantic boundary rather than a local
data declaration. At file level, `util/bigop.v`, `util/bigcat.v`, and
`util/sum.v` each have 333 transitive dependents through the export structure.
Their individual lemmas show little statement fan-out because theorem proof
uses are intentionally excluded. This is expected and is exactly why file and
declaration graphs are both retained.

Preemption roots are lower but still material: `JobPreemptable` has 117
transitive declaration dependents, `TaskMaxNonpreemptiveSegment` 114, and
`FP_policy`/`JLFP_policy` 178/245 respectively.

### Translation order derived from v0.6 only

The only supported full-file order is ascending `file_layers.csv`; files in the
same layer can be prepared in parallel. The early graph-derived phases are:

1. Layer 0 external-only modules (`behavior/time` and the independent `util`
   roots).
2. Layers 1–3 remaining utilities and `util/all`.
3. Layer 4 `behavior/job` plus the independent extrapolated-arrival
   implementation definition.
4. Layer 5 arrival-sequence/SBF foundations.
5. Layers 6–9 schedule, service, supply, readiness, and `behavior/all`.
6. Layers 10–29 model, analysis, results, implementation, and finally
   refinements exactly as enumerated by the CSV.

For declaration-by-declaration work, use ascending `declaration_layers.csv`
instead. It permits a finer start with `instant`, `duration`, `JobType`,
`work`, and `TaskType`, followed by their classes and then schedule/service
definitions. This ordering is computed solely from pinned v0.6 source
references; neither the current Lean tree nor the historical v0.4 translation
influenced it.

### Cycles and unresolved boundaries

- File SCC cycles: **0**.
- Extracted declaration SCC cycles: **0**.
- Internal module references unresolved by inventory: **0**.
- Files with unresolved declaration edges/types: **14**, exactly the
  `implementation/refinements/` group.
- Declarations affected: **239**.
- Cause: current switch lacks the separately packaged `coq-coqeal` dependency;
  the missing boundary is explicitly represented by four CoqEAL imports.

This is an extraction/toolchain limitation for the refinement package, not a
claim that those declarations lack dependencies.

### Reproduction and integrity checks

Run:

```bash
cd Prosa-fei
./Validation/planning/v06_dependency/reproduce.sh
```

The script checks out/verifies the pinned commit, runs all-file `coqdep`, builds
the 343-file main package, regenerates all CSV/JSON/DOT outputs, obtains actual
Rocq type checks, renders SVG when Graphviz is available, and verifies:

- every `.v` file appears exactly once;
- every internal edge points to an existing module;
- graph/SCC coverage includes every node;
- unresolved declaration extraction is listed explicitly;
- the `Prosa-fei/Prosa` Git tree object is unchanged;
- `git diff --check` passes.

No declaration has been translated in this work, and no file under
`Prosa-fei/Prosa/` has been modified.

## Direct answers

1. **Source files:** 357.
2. **Internal file edges:** 1,359.
3. **External boundaries:** 178 direct occurrences, 24 modules, 4 library
   roots.
4. **Public declarations:** 2,439.
5. **Layers:** 30 file layers; 14 extracted declaration layers.
6. **Lowest foundations:** the 11 layer-0 files above; semantic roots are led
   by `instant`, `duration`, `JobType`, `work`, and `TaskType`.
7. **Maximum fan-out:** `util/tactics.v` at file level (346); `JobType` at
   declaration level (1,403 after generated-symbol hardening).
8. **Highest representation risk:** `JobType`, time/work naturals,
   `ProcessorState`, `TaskType`/job-task mapping, arrivals, and the
   service/schedule chain, as quantified above.
9. **Cycles/unresolved:** no cycles and no unresolved internal module edge;
   14 refinement files/239 declarations remain explicitly unresolved at the
   CoqEAL boundary.
10. **Recommended order:** ascending machine-generated file or declaration
    layer only; no current Lean or v0.4 structure was used to choose it.

### 2026-09-20 18:21:39 HKT — Prompt 1 baseline reproduction (superseded declaration counts)

`./Validation/planning/v06_dependency/reproduce.sh` completed successfully.
It regenerated the 357-file inventory, all 1,359 file edges, the 2,429
declaration inventory, all 4,542 extracted declaration edges, and captured
2,190/2,190 expected elaborated main-package declaration types. Completeness,
SCC coverage, strict topological layering, explicit refinement-unresolved
coverage, and type-evidence classification checks all passed. Graphviz produced
`file_dag.svg` (991,677 bytes). `git diff --check` passed, and the production
Lean tree remained exactly Git object
`7426e874bd049e6f007b2695ef13f7209a0a1f8f`.

### 2026-09-20 18:23:35 HKT — Prompt 1 baseline consistency audit (superseded declaration counts)

Final assertions passed: 357 unique source files, 1,359 `coqdep`-verified
internal edges, 2,429 unique public declaration names, 4,542 declaration
statement/body edges, no graph cycles, 2,190 elaborated type checks, and 239
explicit CoqEAL-boundary declarations. `git diff --check` still passes and
`git status` reports no change under `Prosa-fei/Prosa/`.

## Declaration-DAG hardening addendum

### 2026-09-20 18:57:51 HKT — evidence model corrected

The earlier phrase “complete for 2,190 declarations” was too strong. `.glob`
source-reference locations establish explicit dependencies, but absence of a
reference does not establish absence of elaborator-inserted typeclass,
canonical-structure, coercion, or HB dependencies. The file DAG remains
unchanged and authoritative; the declaration DAG is being reclassified as an
explicit fine-grained scheduling aid.

The hardening pass also found a concrete inventory-parser omission: named
`#[export]` and same-line `#[global,...]` instances were not all recognized.
The parser now handles attributes and adds the missing named public instances.
This is a declaration-inventory correction, not a file-DAG change.

Generated-symbol mapping now covers source-span constructors/projections and
unambiguous HB symbols without adding them as public declaration nodes. The
current pre-reproduction result contains 93 generated-symbol mappings and 734
edges using such mappings. Seventy-one referenced local/generated symbols have
no unambiguous public owner and remain explicitly unresolved rather than being
guessed.

The entire pinned tree contains one `Defined.` occurrence: the anonymous global
`RewriteRelation le` instance in `util/setoid.v`. It has zero proof-body
references and is not a named public inventory node, so no named computational
body edge was lost. The extractor nevertheless now extends any future named
computational `... Proof ... Defined` span through `Defined.`.

### 2026-09-20 19:08:32 HKT — hardened clean reproduction passed

The hardened `reproduce.sh` completed from the pinned source and captured
2,200/2,200 buildable elaborated declaration types. Final statuses are:

```text
FILE_DAG_STATUS = VERIFIED_COMPLETE_FOR_PINNED_SOURCE

DECLARATION_DAG_STATUS =
VERIFIED_EXPLICIT_TRANSLATION_RELEVANT_DEPENDENCIES
WITH_DOCUMENTED_IMPLICIT/GENERATED LIMITATIONS
```

The file graph is semantically unchanged: comparison with the Prompt 1
baseline confirms the exact same 1,359 edge identities and the same layer for
all 357 files (30 layers, zero cycles). Generated CSV files now use canonical
LF line endings and SCC traversal is deterministic; these are serialization
changes only.

The final declaration inventory/graph contains:

- 2,439 named public source declarations: 2,200 elaborated main-package
  declarations plus 239 explicit CoqEAL-boundary declarations;
- 4,628 explicit/mapped direct edges: 3,079 type, 1,329 body, 91
  structure-field, and 129 instance edges;
- 3,916 `EXPLICIT_GLOB_DEPENDENCY` edge occurrences;
- 3,263 `ELABORATED_TYPE_CONFIRMED` edge occurrences (confirmation of the
  dependent final type, not proof of edge-set completeness);
- 734 `GENERATED_SYMBOL_MAPPED` edge occurrences;
- 93 generated-symbol mappings: 59 projections, 21 constructors, and 13 HB
  generated definitions;
- 71 referenced local/generated symbols deliberately left unresolved because
  no unique public source owner can be justified;
- confidence: 611 `HIGH_EXPLICIT_AND_GENERATED`, 1,589 `EXPLICIT_ONLY`, and
  239 `UNRESOLVED_EXTERNAL` declarations.

The authoritative scheduling rule is now explicit: `file_layers.csv` is the
mandatory readiness criterion. `declaration_layers.csv` may refine ordering
only inside an already-ready file context. A missing declaration edge never
establishes independence from implicit instance/canonical/HB resolution.

Detailed evidence is in `declaration_dependency_method.md` and the requested
14-declaration chain audit is in `foundation_dependency_audit.md`. The latter
includes each actual elaborated Rocq type, official source body, direct edges,
generated-symbol mappings, unresolved risk, and confidence classification.
`git diff --check` passes, and no path under `Prosa-fei/Prosa/` changed.

### 2026-09-20 19:11:41 HKT — final hardening audit

After the last method/manifest update, a further full reproduction passed:
2,200/2,200 elaborated checks, 357/357 file coverage, all declaration evidence
classifications, the single zero-reference `Defined.` case, all 93 generated
mappings, and all 14 foundational audit entries were checked again.
`HARDENING_FINAL_AUDIT_PASS` and `git diff --check` both succeeded. Production
Lean remains untouched.
