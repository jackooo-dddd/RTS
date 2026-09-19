# Prosa/RTS Rocq→Lean Translation Validation Prototype

**Experiment started:** 2026-09-19 08:32 HKT  

**Validation date:** 2026-09-19 (Asia/Hong_Kong)  
**Repository commit at start:** `051afc1ae02ca2a4c7d0ffa62f0fcc14a1bc5c03`  
**Scope:** modern Prosa v0.6 translation only; `Classic/` and the known
`service_in`/`service_on`/`supply_on`/`supply_in`/`completes_at` mismatch chain
are excluded.

This report distinguishes kernel-checked results from conditional results and
engineering analysis. A target is called certified only when its certificate
mentions the actual declaration imported from the compiled Lean artifact and
Rocq accepts the certificate without an uncertified semantic premise.

## Current machine-checked baseline

The final unified actual Lean export, `export/RTSValidation.out`, was
successfully imported by `rocq-lean-import` into Rocq 9.3 as
`rocq/ImportedEasy93.vo`. After the unified artifact changed, all dependent
bridge files were rebuilt in dependency order; this eliminated stale `.vo`
fingerprint errors.

Already kernel-checked and retained for the final prototype:

| Target | Result | Main correspondence |
| --- | --- | --- |
| `instant` | CERTIFIED | structural Rocq `nat` ↔ imported Lean `Nat` isomorphism |
| `duration` | CERTIFIED | structural Rocq `nat` ↔ imported Lean `Nat` isomorphism |
| `work` | CERTIFIED | structural Rocq `nat` ↔ imported Lean `Nat` isomorphism |
| `job_cost` | PARAMETRICALLY_CERTIFIED | canonical imported class record; projection commutes |
| `job_arrival` | PARAMETRICALLY_CERTIFIED | canonical imported class record; projection commutes |
| `job_deadline` | PARAMETRICALLY_CERTIFIED | canonical imported class record; projection commutes |
| `arrival_sequence` | PARAMETRICALLY_CERTIFIED | pointwise `seq` ↔ imported `List` relation |
| `arrivals_at` | PARAMETRICALLY_CERTIFIED | `seq`/`List` plus imported equality observation |
| `arrives_at` | PARAMETRICALLY_CERTIFIED | membership and equality observation |
| `has_arrived` | PARAMETRICALLY_CERTIFIED | membership plus imported Nat order |
| `arrived_before` | PARAMETRICALLY_CERTIFIED | membership plus imported Nat `<` |
| `arrived_between` | PARAMETRICALLY_CERTIFIED | membership plus imported Nat `≤`/`<` |
| Ideal `scheduled_in` | CERTIFIED | Unit-core surjection, Option-state relation, actual `scheduled_on` |
| Ideal `scheduled_at` | CERTIFIED | composition over actual imported `scheduled_in` |
| theorem `scheduled_at_def` | CERTIFIED_WITH_PROP_SPROP_BRIDGE | bidirectional statement correspondence |

No production Lean file was modified for these results.

## 2026-09-19 theorem-level prototype work

The production theorem pair selected for the first RTS theorem validation is:

- Rocq v0.6: `prosa.analysis.facts.model.ideal.schedule.scheduled_at_def` from
  `analysis/facts/model/ideal/schedule.v`;
- Lean: `Prosa.Analysis.Facts.Model.Ideal_schedule.scheduled_at_def` from
  `Prosa/Analysis/Facts/Model/Ideal_schedule.lean`.

This is a genuine RTS statement about an ideal processor schedule. It depends
on jobs, instants, schedules, job equality, and `scheduled_at`, but does not
enter the excluded service/supply representation chain.

The definition-level `rocq/ScheduledAtCertificate.v` composes the closed Ideal
`scheduled_in` certificate with the actual imported production `scheduled_at`.
Rocq 9.3 accepted `ideal_scheduled_at_certificate`. `Print Assumptions` lists
only the importer foundation already present for the imported artifact
(definitional UIP declarations, imported `propext`, selected `PrimInt63`
primitives, `Quot_sound`, and `Classical_choice`); it contains no
validation-specific semantic premise. Status: **CERTIFIED**.

During compilation this certificate exposed only stale unified-artifact
dependencies and two missing explicit validation imports. Rebuilding the
dependency chain and making those imports explicit fixed it. The production
translation remains unchanged.

### Prop/SProp boundary design

`rocq-lean-import` maps Lean `Prop` to Rocq `SProp`. The reference `lf-lean`
implementation represents an `SProp` proposition in ordinary `Prop` through
an inhabitance wrapper and uses additional axioms when it needs a full
*sort-level isomorphism* `Prop ≅ SProp`.

For this prototype the intended theorem semantics is truth/inhabitance, not
equality of the universes themselves. The implemented bridge uses the smaller
lf-lean-style interface

```text
StrictlyInhabited P : SProp
prop_sprop_trusted_elim : StrictlyInhabited P -> P
PropSPropRel P Q := (P -> Q) * (Q -> P)
```

in `rocq/PropSPropBridge.v`. The Prop-elimination principle is a single,
isolated axiom because Rocq intentionally forbids eliminating arbitrary
`SProp` evidence into `Prop`. `Print Assumptions` exposes it as
`prop_sprop_trusted_elim`; no certificate depending on it is presented as
axiom-free.

### Actual theorem result

`rocq/RTSTheoremCertificate.v` establishes the semantic correspondence for
the real theorem pair `scheduled_at_def`. The proof is compositional: it uses
the already certified Ideal `scheduled_at` observation, the Option-state
equality observation, and a reusable Boolean-equality bridge. It does **not**
use either theorem's proof to prove statement equivalence.

The actual compiled Lean theorem type is present as
`Prosa_Analysis_Facts_Model_Ideal_schedule_scheduled_at_def`. A separate
kernel-checked witness confirms that this imported constant has exactly the
statement used by the correspondence certificate. Its proof body is exported
as opaque/axiomatic in statement-validation mode; consequently that witness's
assumption list contains the imported theorem constant, while
`scheduled_at_def_statement_certificate` itself does not.

`Print Assumptions scheduled_at_def_statement_certificate` contains the usual
importer foundation plus exactly the declared theorem trust boundary
`prop_sprop_trusted_elim`. Status:
**CERTIFIED_WITH_PROP_SPROP_BRIDGE**.

The Rocq 9.3 build uses `rocq/OriginalIdealScheduleSlice.v`, a verbatim replay
of the two relevant v0.6 declarations and proof scripts from
`analysis/facts/model/ideal/schedule.v`, with unrelated declarations and broad
re-export imports omitted. The source replay itself is closed under the global
context. This workaround is necessary because a full v0.6 rebuild on Rocq 9.3
currently encounters compatibility failures in unrelated `util/list.v` and
`util/div_mod.v` proofs.

The production Lean module also required a declaration-free validation build
shim for the broad `Prosa.Util.All` import. The unchanged production
`Ideal_schedule.lean` then compiled successfully. No production declaration
was replaced or modified.

## Final validation matrix

| Target | Actual Lean imported? | Own proof | Dependency closure | Assumptions | Mutation | Status |
| --- | --- | --- | --- | --- | --- | --- |
| `instant`, `duration`, `work` | yes | pass | closed | importer foundation | n/a | CERTIFIED |
| Job projections (3) | yes | pass | canonical representation map | importer foundation | n/a | PARAMETRICALLY_CERTIFIED |
| arrival targets (6) | yes | pass | explicit sequence/order relations | importer foundation | n/a | PARAMETRICALLY_CERTIFIED |
| Ideal `scheduled_in` | yes | pass | closed | importer foundation | rejected polarity mutation | CERTIFIED |
| Ideal `scheduled_at` | yes | pass | closed | importer foundation | inherited | CERTIFIED |
| `scheduled_at_def` theorem | yes, exact type | pass | closed modulo declared sort boundary | `prop_sprop_trusted_elim` + importer foundation | compositional Bool equality | CERTIFIED_WITH_PROP_SPROP_BRIDGE |

The machine-readable declaration-by-declaration mapping is
`mapping/rts_validation_targets.yaml`.

## Toolchain and provenance

- translated repository commit: `051afc1ae02ca2a4c7d0ffa62f0fcc14a1bc5c03`;
- original Prosa source: release `0.6`, peeled source commit
  `414e66760333eaa4ef78c685bcf53291c527a548`;
- Lean: `4.33.1`, commit
  `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`;
- Mathlib: `v4.33.1`;
- lean4export base commit:
  `c9f8373f8a37a65c0ed9bfd20480a3d7481a163e`, plus the checked-in
  statement-only patch for the selected theorem;
- rocq-lean-import commit:
  `c9f43ad5c6e8b82d96e50cb5677157bc9cf581e9` with the previously recorded
  Rocq-9.3/dependent-projection compatibility patches;
- Rocq: `9.3+rc1`, OCaml `4.14.2`.

Artifact fingerprints after the final successful run:

```text
789da9fe0fcc96b448460406d107036f4867b98ecbd18b96cae1da78ea685105  export/RTSValidation.out
e750f470a245a464cdb0c288530cbaab04407fe392da89dc1cb4f22ffd65aa9f  rocq/ImportedEasy93.vo
```

The importer log reaches the selected actual theorem at legacy-export line
120887 and ends with `Done!` (1,899 entries and 106,665 expression nodes).
The native stack is raised to 65,520 KiB because this legacy importer performs
deep recursive conversion.

## Assumption audit

For the definition certificates, `Print Assumptions` reports only the importer
foundation: definitional UIP for imported equality-related inductives,
imported `propext`, selected `PrimInt63` primitives, `Quot_sound`, and
`Classical_choice`. There is no validation-specific semantic hypothesis.

For `scheduled_at_def_statement_certificate`, the same list additionally
contains exactly:

```text
prop_sprop_trusted_elim : forall P : Prop, StrictlyInhabited P -> P
```

The separate imported-statement witness additionally lists
`Prosa_Analysis_Facts_Model_Ideal_schedule_scheduled_at_def`, as expected
because statement-only export represents that opaque theorem proof as an
axiom. The semantic correspondence certificate itself does not depend on this
axiom. The original Rocq source replay is `Closed under the global context`.

The driver rejects `Admitted`, `admit`, and Lean `sorry`, and rejects every
`Axiom` outside the single named declaration in `PropSPropBridge.v`.

## Reusable bridge coverage

| Reusable bridge | Downstream targets in this prototype |
| --- | ---: |
| Rocq `nat` ↔ imported Lean `Nat` | 10 |
| `eqType` carrier/equality ↔ `Type + DecidableEq` | 8 |
| MathComp `seq` ↔ imported Lean `List`, membership | 4 |
| Nat `≤` / `<` and Boolean conjunction | 3 |
| finite existential / Lean `decide (Exists ...)` | 2 |
| Ideal Option-state + Unit-core relation | 3 |
| Boolean equality preservation | 1 theorem, reusable |
| isolated Prop/SProp truth bridge | 1 theorem, reusable |

## Mismatches and missing translations

No semantic mismatch was found in the 15 selected targets. The known
`service_in`/`service_on`/`supply_on`/`supply_in`/`completes_at` representation
problems were deliberately not reclassified or hidden; they remain outside
this validated slice. No production Lean file was changed.

The full Rocq v0.6 library is not yet cleanly rebuildable on Rocq 9.3 because
unrelated legacy proofs in `util/list.v` and `util/div_mod.v` need compatibility
maintenance. Likewise, the broad translated Lean import aggregator pulls in
unrelated proof failures under the pinned modern Mathlib. These are build
compatibility blockers, not evidence against the selected declarations. The
source-extracted Rocq replay and declaration-free Lean import shim are explicit
prototype boundaries and must remain visible in any paper claim.

## Reproduction

From `Prosa-fei/Validation`:

```bash
./scripts/validate_rts_translation.sh
```

This checks and imports the committed actual artifact, compiles every reusable
bridge and certificate, performs the escape-hatch audit, prints assumptions,
runs the scheduled-in negative test, and emits the 15-target summary. To
recompile production Lean dependencies and regenerate the export first:

```bash
REEXPORT=1 ./scripts/validate_rts_translation.sh
```

Environment paths can be overridden with `MATHLIB_DIR`, `LEAN4EXPORT_SRC`,
`ROCQLI_SRC`, `PROSA_ROCQ_SRC`, and `IMPORT_OPAM_SWITCH`.

## Research conclusion

The prototype demonstrates theorem-level 1:1 translation validation against
an actual compiled Lean artifact. The result is not source-text comparison:
the Lean constants are exported and imported, the statement correspondence is
derived from reusable representation relations, and Rocq's kernel checks the
certificate. For theorem propositions, the result is honestly labeled with
the isolated Prop/SProp trust boundary.

The method is extensible to further Prosa declarations when their dependency
representations are covered. The next high-value step is not another one-off
target; it is to generalize the statement-only exporter selection and source
slice generation, then add reusable relations for more schedule/state models.
The known service/supply mismatch family should remain a separate translation
repair investigation.
