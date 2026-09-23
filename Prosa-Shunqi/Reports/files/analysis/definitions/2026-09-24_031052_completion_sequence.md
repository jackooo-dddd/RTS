# `analysis/definitions/completion_sequence.v`

Authoritative source: Prosa v0.6 commit
`414e66760333eaa4ef78c685bcf53291c527a548`.
Canonical first-work timestamp: `2026-09-24 03:10:52 +08:00`.
This report records progress; machine status/manifest alone determine acceptance.

## 2026-09-24 03:10:52 +08:00 — selected as next READY file

The order document ranks this file 37 (layer 8), immediately after the now
published Rank 36. The authoritative file DAG reports one direct internal
dependency, `behavior/service.v`, which has accepted whole-file evidence.
The v0.6 inventory contains exactly one public `Definition`,
`completion_sequence`; the migration table marks it `NEW_TRANSLATION` with
no credible v0.4/current-Lean candidate. The source returns the ordered
list of jobs from `arrivals_up_to arr_seq t` satisfying Boolean
`completes_at sched j t`; List order and multiplicity are observable.
No Lean production declaration or semantic certificate for this file has
been accepted yet. Cumulative accepted coverage is 316/2439 declarations
and 35/357 files.

## 2026-09-24 03:16:18 +08:00 — Lean candidate compiled with verified dependency reuse

The new production candidate defines `completion_sequence` as a function
from time to `List.filter` of `arrivals_up_to`, with the actual accepted
`completes_at` Boolean predicate; it preserves source order and
multiplicity. An actual Lean preflight confirmed that `arrivals_up_to`
requires only `DecidableEq Job`, while `completes_at` requires `JobCost`
and the schedule/processor state. A project-root `lake env lean` attempt
failed because this checkout deliberately lacks the accepted Service `.olean`
there; no source error was inferred. The approved FILE_VALIDATE producer
then verified and materialized the complete 25-module accepted Service
dependency closure into an isolated work directory (`VERIFIED_CACHE`), and
the new target compiled against that closure. This is **Lean compilation
only**, not semantic acceptance. Next: actual target export/import and
compositional Rocq certificate using already accepted `arrivals_up_to`,
`completes_at`, and list-filter operation relations.

## 2026-09-24 03:25:17 +08:00 — official body replayed; importer scalability under test

The source extractor regenerated `completion_sequence` from the pinned
official file with the declaration body byte-identical to the source
inventory block (SHA-256 `e26ab0af…`); its Section context includes
`JobCost`, `ProcessorState`, `arr_seq`, and `sched`. The extracted source
compiled using the already accepted Service source `.vo` closure. The
actual freshly compiled Lean target exported with its complete unprojected
body as `CompletionSequence.out` (4,161,709 bytes; SHA-256
`c54e38df…`). `rocq-lean-import` is still running at this timestamp,
using one CPU core and roughly 1.1–1.3 GiB memory while traversing deep
Nat/Service transitive computation and proof-field dependencies. This is
an **importer scalability observation**, not a semantic mismatch or a
published result. If the import cannot finish promptly, the next attempt
will use an already approved kernel-guarded computation projection; no
definition body or acceptance gate will be weakened.

## 2026-09-24 03:29:07 +08:00 — unprojected import stopped at a concrete scalability point

The 4.0 MiB unprojected export has 181,128 lines. Rocq's importer remained
at line 177,929 (`Nat.Internal.Linear.ExprCnstr.denote_toNormPoly`) for over
ten minutes at about 100% of one CPU core and 1.1–1.3 GiB resident memory;
it produced no `.vo`. I stopped this **validation-only import process** to
avoid spending further time on a transitive Mathlib proof/computation
implementation that is not part of this one-definition correspondence.
This is `BLOCKED_BY_IMPORTER_SCALABILITY` for the naive export mode, **not**
`FAILED_SEMANTIC_EQUIVALENCE`. The source body, Lean candidate, and all
acceptance requirements are unchanged. Next attempt: reuse the already
approved Service computation projections and ArrivalSequence/Bigcat
computation interfaces in a combined export root, with their Lean kernel
guards and exact compiled target constant binding.

## 2026-09-24 03:37:05 +08:00 — combined actual-artifact import succeeded

The validation-only combined export root imports the freshly compiled
production `CompletionSequence.olean` and the previously accepted Service,
ArrivalSequence, and Bigcat computation interfaces. A deterministic config
generator merged the approved interfaces while preserving the actual target
definition body. The resulting `CompletionSequenceCombined.out` is 2,766,987
bytes; its export metadata records 49 targets, **zero statement-only theorem
targets**, nine proof-bodied computation interfaces, and twelve Service body
projections with Lean kernel `rfl` guards. Rocq 9.3 successfully imported it
as `ImportedCompletionSequenceCombined.vo` in about 34 seconds. This removes
the naive-export importer scalability blocker for the current interface,
but is **not** a semantic certificate. Next: inspect the imported target's
exact type/body, replay accepted lower-level correspondences against this
artifact identity, and prove the ordered List-filter composition.

## 2026-09-24 03:46:07 +08:00 — compositional correspondence compiled

`CompletionSequenceTypeInspection.v` printed the imported compiled target:
it is an `arrival_sequence` whose body is `List_filter` with the actual
imported `completes_at` predicate applied to imported `arrivals_up_to`.
`CompletionSequenceSourceInspection.v` printed the elaborated official
source slice and its MathComp ordered `filter` body. The accepted Service
and ArrivalSequence proof sources were mechanically replayed with only the
imported module identity changed, then **recompiled** against this combined
artifact. Their operation proofs compiled, including
`completes_at_correspondence`, `arrivals_up_to_correspondence_certificate`,
and `ar_filter_related`. The new
`Validation/certificates/analysis/CompletionSequenceCorrespondence.v`
composes those relations; Rocq 9.3 accepted its proof and `Print Assumptions`
reported only the expected importer foundations plus
`PropSPropFoundation.interpret_strict`. This is a successful kernel proof,
but final fail-closed assumption/self-dependency audit, exact-type guard,
provenance publication, and status update have not yet run. Formal accepted
coverage therefore remains **316/2439 declarations, 35/357 files**.

## 2026-09-24 03:53:57 +08:00 — whole-file publication accepted

The Lean audit printed the actual compiled definition and reported only
`propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx` or custom Lean
axiom appeared. The separate Rocq assumption audit classified the sole
certificate as `CERTIFIED_WITH_PROP_SPROP_FOUNDATION` with zero semantic
premises, zero statement-only dependencies, no source/target self-dependency,
and no unexpected axiom. The publisher rechecked the pinned source and
elaborated-type fingerprint, byte-identical extracted computational block,
accepted Service/ArrivalSequence producer hashes, Lean/Mathlib/Rocq/tooling
pins, fresh `.olean` → export → imported `.vo` ordering, actual target/body
binding, all replayed proof `.vo` files, and `git diff --check`. Machine
manifest/status files are
`Validation/planning/v06_pipeline/analysis_completion_sequence_module_{manifest,status}.json`.
The complete one-declaration file is now `ACCEPTED_V06_FILE`; cumulative
accepted coverage is **317/2439 declarations, 36/357 files**. The only
non-kernel trust boundary beyond the established importer foundations is
`PropSPropFoundation.interpret_strict`, inherited through the certified
Service/list-operation dependencies.
