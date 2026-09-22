# behavior/arrival_sequence.v — canonical translation report

First experiment timestamp: **2026-09-22 22:29:29 +08:00**  
Latest progress update: **2026-09-22 23:56:13 +08:00**

## Current status

Rank 23 is dependency-ready: `behavior/job.v` and `util/notation.v` are both
`ACCEPTED_V06_FILE`. The authoritative file has 14 declarations. Translation
and semantic validation are in progress; none of these declarations is yet
counted as accepted.

## Initial representation audit

- `arrival_sequence` is an instant-indexed ordered sequence, hence Lean
  `instant → List Job`; order and multiplicity remain observable.
- The source `arrives_at`, `has_arrived`, `arrived_before`, and
  `arrived_between` are MathComp Boolean computations. The historical Lean
  candidate rendered several of them as `Prop`; the v0.6 translation must keep
  their result as `Bool` under the approved policy.
- `arrives_in`, consistency, uniqueness, and validity are propositions whose
  Boolean subexpressions are reflected explicitly.
- `arrivals_between` uses the already accepted half-open ordered `bigCat`
  representation, not a `Finset`; `arrivals_between_P` is the new-in-v0.6
  filtered-list declaration missing from the historical candidate.
- Every source `JobType` boundary retains explicit Lean `DecidableEq`
  evidence.

## Planned correspondence reuse

The target should compose existing certified relations for Job equality,
instant/Nat order, ordered seq/List, membership, Nodup, Bool truth, List
filter, and half-open big concatenation. Only an artifact-local adapter for the
new compiled module should be needed; no new global representation decision is
planned.

Evidence starts at
`Validation/planning/v06_pipeline/behavior_arrival_sequence_selection.json`.
This report will be updated in place; no second report will be created for the
same source file.

## 2026-09-22 22:36:51 +08:00 — complete Lean candidate written and compiled

All 14 authoritative public declarations now have production candidates in
`Prosa/Behavior/Arrival_sequence.lean`, in source order:

```text
arrival_sequence
arrivals_at
arrives_at
arrives_in
consistent_arrival_times
arrival_sequence_uniq
valid_arrival_sequence
has_arrived
arrived_before
arrived_between
arrivals_between
arrivals_up_to
arrivals_before
arrivals_between_P
```

The whole candidate file passes an isolated Lean 4.33.1 compile. The produced
preflight `.olean` has SHA-256
`49a0cd72dd999b09adee6f0eaadddde549565c65da522c2f8a688a7ef98baeab`;
the current Lean source has SHA-256
`0fdb7632034b9b5fd3cd88ce739dffad38be4e8c4a3cafd8df718cb762092355`.
This is compile evidence only, not semantic acceptance.

The translation audit found a material reason not to copy the historical Lean
file blindly: the official v0.6 declarations `arrives_at`, `has_arrived`,
`arrived_before`, and `arrived_between` elaborate to `bool`. The new candidate
therefore preserves Boolean computation, while proposition-valued declarations
such as `arrives_in`, consistency, uniqueness, and validity remain `Prop`.
`arrivals_between_P`, which has no historical candidate, is translated as an
ordered, multiplicity-preserving list filter over the certified half-open
`bigCat` representation.

Current declaration state:

| Dimension | Result |
|---|---:|
| authoritative declarations mapped | 14 / 14 |
| Lean candidates written | 14 / 14 |
| isolated Lean compile | PASS |
| semantic certificates accepted | 0 / 14 |
| file acceptance | `IN_PROGRESS` |

The next gate is the actual compiled-type/body audit followed by one frozen
export/import preparation and compositional Rocq certificates. Until those
gates and the fail-closed assumption audit pass, cumulative accepted coverage
remains 22 files and 209 declarations.

## 2026-09-22 23:30:08 +08:00 — actual-artifact and source-fidelity preflight complete

The missing progress since the Lean candidate compile is now recorded here.
This section is pre-publication evidence; it does not change accepted coverage.

### Official Rocq source acquisition

The exact pinned `behavior/arrival_sequence.v` was compiled under Rocq 9.3
without changing any declaration. The first attempt exposed a compatibility
surface issue: the earlier Job-only validation shim for `util/all.v` did not
re-export MathComp `seq`, which Arrival Sequence genuinely needs. A new
declaration-free compatibility import surface was isolated at
`Validation/fixtures/translation_order/source_compat/arrival_sequence/util/all.v`.
It exports only the external MathComp modules required to elaborate the
byte-identical official source; it defines no replacement Prosa object.

The successful clean source run is
`Validation/.work/runs/arrival_sequence_source_preflight.EQ9aL9`.
The resulting official `arrival_sequence.vo` SHA-256 is
`539b3e98d342a81880239a99032fd168af4d14be8c0a1c99c9fb4ddffaabf10d`;
the compatibility surface SHA-256 is
`af3dd3534fababa8e8ce3c0a0f75a6fdaf8b4abda1c4edab0fd40bd70d70a3e2`.

### Actual compiled Lean export and Rocq import

`LeanArrivalSequenceAudit.lean` checked and printed all 14 production
declarations from the isolated `.olean`. The four proposition-valued
definitions whose bodies use proposition extensionality report only `propext`;
the remaining ten are axiom-free. No declaration contains `sorryAx` or a
custom axiom.

The full definition bodies were then exported directly; no theorem
statement-only boundary, normalization, body projection, or hand-written
target model was used. Evidence from run
`Validation/.work/runs/arrival_sequence_lean_preflight.N4LdS4` is:

| Artifact | SHA-256 / result |
|---|---|
| production Lean source | `0fdb7632034b9b5fd3cd88ce739dffad38be4e8c4a3cafd8df718cb762092355` |
| isolated production `.olean` | `49a0cd72dd999b09adee6f0eaadddde549565c65da522c2f8a688a7ef98baeab` |
| `ArrivalSequence.out` (137,823 bytes) | `e79f965ef4098667040afdc50d6dbe057b9997380c2d25309f52aa8e8a49923b` |
| imported `ImportedArrivalSequence.vo` | `7dedc48b5d88080e1c94b772bdb3a0f91dc43c810c13110bfe7585ee01dfb5a8` |
| export | PASS, 59.11 s |
| Rocq import | PASS, 1.55 s |

`ArrivalSequenceImportedAudit.v` prints the actual imported constants and
their bodies. In particular it confirms that membership is implemented by the
imported List predicate plus `decide`, order predicates use imported Nat
decisions, `arrivals_between` calls the already translated ordered `bigCat`,
and `arrivals_between_P` calls the imported List filter.

### Reusable correspondence layer

The existing artifact-adapter generator produced
`ArrivalSequenceBaseAdapter.v`, bound to this imported module. It kernel-checks
Bool truth/roundtrips, `eqType`/`DecidableEq`, ordered seq/List roundtrips, and
membership correspondence. The generated source SHA-256 is
`c306828754819c1b481ce0e423ab7f2a46b490c1619f0eac226a3eeebf6bddef`;
its preflight `.vo` SHA-256 is
`5f48771f6abd57df05fb40e779cc94328211ba36e06c9811aa9ed9f5f6b002ce`.
This reuses the certified correspondence DAG rather than restating Bool/List
semantics in each of the 14 target certificates.

The preflight also detected that a previously published
`ImportedSubadditivity.vo` had been built against an older
`LeanImport.Lean` foundation. Rocq correctly rejected the inconsistent
assumptions. The validator re-imported the unchanged accepted `.out` with the
current importer, producing transient SHA-256
`9d934dfd1a8c9f5773146cf5f9f97e766e7c39ace3d2a7f371fd1b3890b21452`.
No stale `.vo` was accepted.

### Current semantic gate

Actual artifact import is therefore no longer the blocker. Work is now at the
operation/certificate layer: expose kernel-checked equations for actual
`bigCat` and List filter computation, compose the existing Nat, JobArrival,
Nodup, membership, Bool, List and Prop/SProp relations, then compile and audit
14 declaration certificates. No declaration is published until the unified
assumption and source/target self-dependency audit passes.

## 2026-09-22 23:50:16 +08:00 — all 14 correspondence proofs kernel-compile

The validation-only computation interface now places the actual production
Arrival Sequence definitions and seven already audited `bigCat`/append/filter
equations in one compiled export environment. The new export is 463,638 bytes
with SHA-256
`8dd59d13fe7d6cc46b37138f1d54c732afaa0f8b7194d0d87ed60de28b9f88f1`;
the Rocq import SHA-256 is
`8cb4e8ec7c29de129083ae941a543d8dfa68446c1d39cce8b2878789b03fabbb`.
The equations are Lean theorem bodies checked against the actual production
operations, not statement-only assumptions or a hand-written target model.

`ArrivalSequenceOperations.v` adds the smallest missing reusable layer:

- Boolean conjunction and `decide` correspondence;
- ordered List append, filter, equality, membership and `uniq`/`Nodup`;
- Nat `<=`/`<` decision correspondence;
- the artifact-local `JobArrival` projection relation;
- arrival-sequence function relation;
- half-open MathComp `\cat_(m <= i < n)` versus the actual imported `bigCat`;
- structural `forall`, `exists`, conjunction and implication combinators.

Its source/compiled hashes are
`b3d8a9f93976846f1777182c55f59b73872f912d8a2534c69e65d1dcbd1778cc`
and
`8151aa651dadfa57626d095f44c750cdcad6e2e34d5af1aac7998a364c936fb5`.
The layer reuses the existing certified Nat, Bool, eqType, seq/List,
membership and Prop/SProp DAG; it introduces no semantic premise.

`ArrivalSequenceCorrespondence.v` then composes that layer into one
independent certificate for every authoritative declaration:

```text
arrival_sequence          PASS (Rocq kernel compile)
arrivals_at               PASS
arrives_at                PASS
arrives_in                PASS
consistent_arrival_times  PASS
arrival_sequence_uniq     PASS
valid_arrival_sequence    PASS
has_arrived               PASS
arrived_before            PASS
arrived_between           PASS
arrivals_between          PASS
arrivals_up_to            PASS
arrivals_before           PASS
arrivals_between_P        PASS
```

The certificate source SHA-256 is
`5b5f0de2cf8a7f00dbbd6809c8e96ef8ae0d368a0b87801f8a3657d9493ff453`;
the compiled `.vo` SHA-256 is
`b1fbb692786ed6d6f51fc30ac4a8d16477cca0af83ee3a7e6c8fdd91a63ccb5f`.
Each proof relates the source/target statement structure and operations; none
invokes a source theorem or target theorem constant to establish its own
correspondence.

This is `SEMANTIC_PROOF_COMPILED`, not yet `ACCEPTED`. The remaining gates are
the separate exact-type audit, fail-closed automatic classification of all
`Print Assumptions` blocks (including target/source self-dependency), and one
formal clean prepare/check/finalize publication run. Until those finish,
machine acceptance remains 22/357 files and 209/2439 declarations.

## 2026-09-22 23:56:13 +08:00 — exact-type and assumptions pre-audit passes

The separate type-audit module successfully elaborates all 14 official source
constants, all 14 actual imported Lean constants, and the 14 certificate
types that bind the two sides. The fail-closed marked `Print Assumptions`
classifier reports:

| Classification | Count |
|---|---:|
| `CERTIFIED` | 2 |
| `CERTIFIED_WITH_PROP_SPROP_FOUNDATION` | 12 |
| `CONDITIONAL` | 0 |
| `FAILED_ASSUMPTION_AUDIT` | 0 |
| `AUDIT_MISSING` | 0 |

The two foundation-free results are `arrival_sequence` and `arrivals_at`.
Every other result visibly records the approved
`PropSPropFoundation.interpret_strict` boundary. Across all 14 results:

```text
semantic premises              = []
unexpected assumptions         = []
source declaration dependency  = false
target declaration dependency  = false
```

The exact-type audit `.vo`, assumption-audit `.vo`, and classified summary
SHA-256 values are respectively
`1ca139560988ef8f59d8de8cabb80eb9689d1f75b9eb35615a2170e8d37540d8`,
`b32fa2ab875074a0559cc82fe4a18bc14e07c86a647bca53d89ee8694d68f15a`,
and
`45e71aeaae998382bd70eb5decaed750d1c6ce8112bf9639cc7395630fb4957e`.

This was the artifact-bound pre-audit. Formal publication still requires the
workspace validator's clean prepare/check/finalize reproduction and provenance
manifest, so accepted coverage is not incremented yet.

## 2026-09-23 00:08:14 +08:00 — formal validator integration completed

The Arrival Sequence preflight is now connected to the workspace's generic
incremental `prepare → check → finalize` driver.  The file-specific hook binds
the exact source checkout, the previous accepted Job baseline, all 25 freshly
compiled Lean modules, the computation-interface export, both Rocq imports,
the complete certificate DAG, the two assumption policies, and publication
outputs into one content-addressed snapshot.

The hook passed shell syntax and `git diff --check` preflight.  It also retains
the fail-closed checks established by the pre-audit: 14 exact targets, two
foundation-free results, twelve results carrying only the approved
`interpret_strict` boundary, no semantic premise, no source/target
self-dependency, and no unknown assumption.  The next action is the formal
`CLEAN_FULL=1 ... finalize` reproduction; this integration milestone alone
does not change accepted coverage.

## 2026-09-23 00:17:08 +08:00 — clean semantic run passes; publication-only retry required

The first formal `CLEAN_FULL` execution passed every semantic gate. Measured
stage times were: Lean build 419.79s, official source acquisition 4.88s,
actual-artifact export 49.24s, Rocq import 4.98s, certificate compilation
8.33s, and fail-closed assumption audit 0.14s. All output hashes matched the
preflight semantics, including the exact export hash
`8dd59d13fe7d6cc46b37138f1d54c732afaa0f8b7194d0d87ed60de28b9f88f1`.

Publication itself failed in 0.08s because its Python code incorrectly
asserted that the classifier's JSON object keys retained authoritative source
order. The classifier deliberately serializes deterministic/sorted keys; all
14 named records, the 2/12 status counts, empty premise/unexpected sets, and
self-dependency checks were already correct. This is an infrastructure-only
failure, not a semantic or translation failure.

The retry is isolated as a check/publication hook: it removes only that order
assertion, binds the correction into the check fingerprint, and reuses the
hash-verified clean prepare. It will therefore rerun certificates, audit and
publication without repeating Lean build, source acquisition, export, or
import. Coverage remains unchanged until that retry publishes successfully.

<!-- FORMAL_PUBLICATION_BEGIN -->
## 2026-09-23T00:23:01.746837+08:00 — formal clean publication accepted

The workspace-local incremental validator completed a `CLEAN_FULL` prepare
and semantic check, followed by a hash-verified cached finalize for the frozen
production snapshot
`c1d257c3b0ec6199ee42ca57b25a48c34cfea4514dfdd98249295bc68b32b78e`. It freshly compiled 25 Lean modules (the accepted utility
closure, Time, Job, Arrival Sequence, and two actual-artifact computation
interfaces), compiled the exact byte-identical official source chain, exported
the computation interface, imported it into Rocq, rebuilt every certificate,
and ran fail-closed Lean/Rocq assumption audits.

The initial publication-only retry exposed that `CLEAN_FULL` evidence was
sealed but not automatically installed as the canonical cache. An accidental
duplicate build was interrupted, its incomplete temporary directory was not
used as evidence, and the original clean prepare was independently verified
against its descriptor and every output hash before promotion. The successful
finalize then recorded four `VERIFIED_CACHE` hits, zero prepare-stage
executions, 8.11s certificate compilation, 0.14s audit, and 0.11s publication.

Final classification:

| Class | Count |
|---|---:|
| `CERTIFIED` | 2 |
| `CERTIFIED_WITH_PROP_SPROP_FOUNDATION` | 12 |
| semantic premises | 0 |
| source/target self-dependencies | 0 |
| unexpected assumptions | 0 |

The accepted file adds all 14 authoritative declarations. Cumulative machine
coverage is **23 / 357 files** and **223 / 2439 declarations**, with zero
translated-but-not-certified debt. `Prosa-fei/` remained unchanged.

Key formal artifact hashes are the production `.olean`
`49a0cd72dd999b09adee6f0eaadddde549565c65da522c2f8a688a7ef98baeab`, export `8dd59d13fe7d6cc46b37138f1d54c732afaa0f8b7194d0d87ed60de28b9f88f1`,
import `bfa47fc715294d8a77bbf06f9c018843efbe0082463cf3e51a516790385590ef`, and correspondence certificate
`43149e3d24eac9fd2ab0c7821fb3086de43c343769b2ae181659946807bfbbf9`.

Final file status: **ACCEPTED_V06_FILE**.
<!-- FORMAL_PUBLICATION_END -->
