# Easy semantic certificates — 2026-09-18

Experiment start: **2026-09-18 16:04 HKT**

This is an append-oriented report for the low-risk declaration phase. Results
are recorded target-by-target as soon as they are machine checked. Earlier
pilot reports remain historical records and are not overwritten.

## Scope and starting point

- Repository commit actually checked at phase start:
  `49eb92fbe1e0e1cc4e6c049f3f9d7ded9f67e033`.
- Production files below `Prosa-fei/Prosa/`, including `Classic/`, will not be
  modified.
- Excluded in this phase: `service_in`, per-core service/supply,
  `supply_in`, `completes_at`, `TaskMinCost`, and dependent repair work.
- Reused pipeline: Lean 4.33.1 export → actual legacy artifact → patched
  `rocq-lean-import` → Rocq 9.3 RC1 → Rocq kernel certificate.
- Starting machine-checked result: the actual imported
  `Prosa.Behavior.Schedule.ProcessorState.scheduled_in` has a correspondence
  theorem accepted by Rocq, conditional on explicit `core_surjective` and
  `scheduled_on_rel` premises. Its imported body and assumptions are recorded
  in the preceding dated import report.

## Status vocabulary

- **CERTIFIED**: actual imported declaration, kernel-accepted proof, closed
  semantic dependencies, and no validation-specific semantic premise.
- **PARAMETRICALLY_CERTIFIED**: actual imported declaration and generic
  kernel-accepted proof whose parameters are the declaration's intended
  source-level structures/relations, without an unproved target-specific
  semantic hypothesis.
- **CONDITIONAL**: proof passes but at least one target-specific semantic
  dependency remains a premise.
- **FAILED**: an actual semantic mismatch is established.
- **BLOCKED**: toolchain or unresolved dependency prevents a certificate.

## Phase plan

1. Close `scheduled_in` for the concrete ideal processor (`Core = Unit`).
2. Certify the type aliases and Job projection fields using reusable Nat and
   function/record-observation relations.
3. Certify the simple arrival-sequence layer; add reusable sequence/List,
   membership, uniqueness, and range-concatenation bridges only when required.
4. Compose `scheduled_at` only from the accepted `scheduled_in` certificate;
   do not enter the service representation mismatch.

No new machine-checked target result is claimed in this initial entry.

## 16:07 HKT — report/log layout and Ideal export

At the user's request, all 17 existing `.log` files were moved from the report
root into `reports/logs/`. Both verification scripts and every Markdown log
reference were updated. The report root now contains only the three Markdown
reports plus the `logs/` directory.

`mapping/symbols.yaml` was updated so `scheduled_in` no longer carries the
obsolete `BLOCKED` import status. It now records:

- actual artifact imported: yes;
- certificate: `scheduled_in_actual_artifact_bridge`;
- status: **CONDITIONAL**;
- remaining dependencies: `core_surjective` and `scheduled_on_rel`.

The existing `ScheduledIn.out` does not contain the Ideal processor instance.
Without editing any production Lean source, the original modules
`Behavior.Ready`, `Behavior.All`, and `Model.Processor.Ideal` were compiled into
the temporary `/private/tmp/prosa-olean` tree with Lean 4.33.1 and Mathlib
v4.33.1. The legacy exporter at commit
`c9f8373f8a37a65c0ed9bfd20480a3d7481a163e` then exported these actual
declarations:

```text
Prosa.Model.Processor.Ideal.processor_state
Prosa.Model.Processor.Ideal.ideal_scheduled_at
Prosa.Model.Processor.Ideal.pstate_instance
Prosa.Behavior.Schedule.ProcessorState.scheduled_in
```

The resulting `export/IdealScheduledIn.out` contains 120,357 lines and
2,669,540 bytes. Export and Lean compilation both exited 0. This is an actual
Lean artifact, but no Rocq import or semantic certificate is claimed yet.

Although `Ideal.lean` imports `Behavior.All`, the forthcoming certificate will
observe only `Core`, `scheduled_on`, and `scheduled_in`; no service/supply
semantic work is being introduced.

## 16:10 HKT — Ideal actual artifact imported

`rocq/ImportedIdeal93.v` imports the unchanged
`export/IdealScheduledIn.out`. With the same Rocq 9.3/importer pipeline as the
preceding successful experiment, the full import exited 0 and ended with:

```text
line 120357: Prosa.Behavior.Schedule.ProcessorState.scheduled_in

Done!
- 1868 entries (3183 possible instances) (including quot).
- 53 universe expressions
- 12137 names
- 106301 expression nodes
```

The log is `reports/logs/import_ideal_rocq93.log`. It explicitly shows the
actual declarations at legacy-export lines 39, 1106, 114146, and 120357:

- `Prosa.Model.Processor.Ideal.processor_state`;
- `Prosa.Model.Processor.Ideal.ideal_scheduled_at`;
- `Prosa.Model.Processor.Ideal.pstate_instance`;
- `Prosa.Behavior.Schedule.ProcessorState.scheduled_in`.

Artifact fingerprints:

```text
9e4cc11fadf647e3079696740624b468e63b5203d1eb5dcfa456b1ab2769ed01  export/IdealScheduledIn.out
50f6b6daf7bcc1559f65e5e6e7d5bde36c9c84c5efc229c058d86042260e7f6b  rocq/ImportedIdeal93.vo
```

**Machine-checked result:** actual Ideal Lean artifact import **PASS**.

**Not yet claimed:** the concrete semantic theorem still must identify the
imported `Core` as imported `Unit`, construct the core maps, and prove that
Rocq boolean equality on `option Job` corresponds to Lean's imported
`Decidable_decide (s = some j)` under the chosen Job equality relation.

## 16:15 HKT — reusable cross-carrier finite-existential bridge

`ProcessorStateBridge.v` now additionally provides
`scheduled_in_actual_artifact_rel_bridge`. It generalizes the earlier theorem
from a shared Job/State carrier to explicit `JobRel` and `StateRel` relations
between different original and imported representations. The proof still uses
the actual imported `scheduled_in`, MathComp finite enumeration, imported Lean
existence, and `Decidable_decide`; no target-specific model is substituted.

The first compilation exposed and corrected one argument-order error in the
new proof application. The corrected file then compiled under Rocq 9.3 with
exit code 0; output is in
`reports/logs/processor_state_rel_bridge.log`.

**Machine-checked reusable bridge:** cross-carrier finite existential and Bool
decision correspondence **PASS**.

**Coverage so far:** generic `scheduled_in` plus the planned concrete Ideal
instantiation; it will also be the composition point for `scheduled_at`.

## 16:18 HKT — reusable eqType/DecidableEq equality bridge

The first `EqTypeBridge.v` compilation exposed that importing the old
`ScheduledIn.out` and the richer `IdealScheduledIn.out` as separate Rocq
modules creates distinct module-scoped copies of imported `Bool`. These copies
cannot be mixed by conversion. This is an importer artifact-isolation issue,
not a source semantic mismatch.

The active processor bridge, audit, and mutation fixture were therefore moved
to the single superset `ImportedIdeal93` artifact. The historical
`ImportedScheduled93` files remain unchanged for the earlier experiment.

`EqTypeBridge.v` now provides:

- `imported_classical_decidable_eq`, representing a Rocq `eqType` carrier as
  the same Lean carrier plus an imported `DecidableEq`;
- `eqtype_bool_eq_imported_decide`, proving that MathComp boolean equality
  corresponds to the actual imported Lean equality decision.

The proof compiled with Rocq 9.3, with no output/error, after the artifact
unification. It uses the MathComp `eqP` reflection law and imported Lean
equality; no equality isomorphism between `eqType` and `Type` is asserted.

**Machine-checked reusable bridge:** `eqType` boolean equality ↔ imported Lean
`DecidableEq` equality decision **PASS**.

**Representation finding:** `JobType := eqType` → `JobType := Type` is handled
as a carrier-plus-equality-observation relation, exactly as required; it is not
reported as structural equality of the typeclass representations.

## 16:26 HKT — concrete Ideal specialization imported

The legacy importer represents the separately exported small-universe Ideal
instance as `ProcessorState_inst1`, while the separately exported polymorphic
`scheduled_in` expects another universe variant of `ProcessorState`. Directly
applying those two independently rooted imported constants is therefore
ill-typed. This is recorded as a legacy export/import universe-specialization
boundary, not as a Prosa semantic mismatch.

To validate the real application without changing production Lean,
`Validation/lean/IdealScheduledInFixture.lean` was added. Its only definition,
`Prosa.Validation.ideal_scheduled_in`, delegates directly to the existing
production `ProcessorState.scheduled_in` with the existing production
`Ideal.pstate_instance`; it does not reproduce the finite existential.

Lean 4.33.1 compiled the fixture and legacy `lean4export` produced
`export/IdealConcreteScheduledIn.out`. Rocq 9.3 then imported the entire
artifact successfully:

```text
line 117750: Prosa.Behavior.Schedule.ProcessorState.scheduled_in
line 120357: Prosa.Model.Processor.Ideal.pstate_instance
line 120380: Prosa.Validation.ideal_scheduled_in

Done!
- 1869 entries (3184 possible instances) (including quot).
```

The complete log is
`reports/logs/import_ideal_concrete_rocq93.log`. Fingerprints:

```text
62190a57c9fae93b31fb3a4bc8a232eddd9854020260bba0081435580ca589bf  export/IdealConcreteScheduledIn.out
3aa5b65de912822d8796715e693b447c3fe43ac4cb2f4b3140abd337622d5b98  rocq/ImportedIdealConcrete93.vo
```

**Machine-checked result:** actual specialized production call import
**PASS**. The semantic proof and imported-body audit are the next step; this
entry alone is not yet a certificate.

## 16:38 HKT — first concrete CERTIFIED result

Rocq 9.3 accepted `rocq/IdealScheduledInCertificate.v`, including:

- `IdealStateRel`, relating Rocq `option Job` to imported Lean
  `Option_inst1 Job` constructor-by-constructor;
- closed maps between the original MathComp unit core and imported Lean
  `Unit`, with a proved `ideal_core_surjective` theorem;
- `ideal_scheduled_on_rel`, proved from the actual original Ideal
  `scheduled_on`, the actual imported Ideal instance, and the reusable
  equality/Option bridges;
- `scheduled_in_actual_artifact_rel_bridge_inst1`, a reusable version of the
  finite-existential bridge for the legacy importer's small-universe record
  specialization;
- `ideal_scheduled_in_certificate`, whose imported endpoint is the compiled
  `Prosa.Validation.ideal_scheduled_in` specialization and whose unfolded body
  calls the production
  `Prosa_Behavior_Schedule_ProcessorState_scheduled_in_inst1` with the
  production imported Ideal instance.

There is no `core_surjective`, `scheduled_on_rel`, equality-correctness, or
other validation-specific semantic hypothesis in the final theorem. It is
parametric only in the original `Job : eqType` and in related input values,
which is the intended representation interface rather than an uncertified
dependency.

Compilation command exited 0 and the complete output, including
`Print Assumptions ideal_scheduled_in_certificate`, is in
`reports/logs/ideal_scheduled_in_certificate.log`. Reported assumptions are
the importer's established foundations only: definitional UIP for imported
equality/HEq/True/STrue, `propext`, registered `PrimInt63` primitives,
`Quot_sound`, and `Classical_choice`. No validation-specific axiom appears.

| Target | Actual Lean artifact imported? | Source identified? | Relation | Own proof | Dependency closure | Assumptions | Status |
| --- | --- | --- | --- | --- | --- | --- | --- |
| Ideal `scheduled_in` | yes | yes, Prosa v0.6 `behavior/schedule.v` + `model/processor/ideal.v` | `IdealStateRel`, imported equality, Unit-core bijection, `ImportedBoolRel` | pass | closed | clean relative to importer foundation | **CERTIFIED** |

Reusable bridges added so far:

1. cross-carrier finite existential / `Decidable_decide` bridge, including
   the `_inst1` universe specialization — currently covers generic
   `scheduled_in`, Ideal `scheduled_in`, and planned `scheduled_at`;
2. `eqType` carrier + equality observation ↔ Lean `Type + DecidableEq` —
   currently covers Ideal scheduling and is intended for arrival membership;
3. Rocq `option` ↔ imported Lean `Option_inst1` constructor relation and Some
   equality congruence/injectivity — currently covers Ideal scheduling.

No production Lean file was modified.

## 16:38 HKT — unified easy-target artifact imported

To keep all downstream bridges in one imported `Bool`/`Nat`/`List` universe,
the following actual declarations were exported together into
`export/EasySemanticTargets.out`: both Time aliases, `work`, all three Job
field projections, all requested Arrival_sequence declarations, generic
`scheduled_in`, the certified Ideal specialization, and `scheduled_at`.

The full Rocq 9.3 import exited 0. The log
`reports/logs/import_easy_targets_rocq93.log` lists every requested source
declaration and ends with:

```text
Done!
- 1897 entries (3216 possible instances) (including quot).
- 53 universe expressions
- 12252 names
- 106614 expression nodes
```

Fingerprints:

```text
90920bacbb7908f400809f7eef520c992f1f2ea0540375ca6d188859ec00489b  export/EasySemanticTargets.out
417422d92903e1668bcf6ee8874f12511d3d3c1a806a98a689e2e4374b3d0e12  rocq/ImportedEasy93.vo
```

The active reusable bridges were migrated to this single superset artifact.
No semantic proof changed; this prevents cross-artifact duplicate-type
conflicts during the Time/Job/Arrival/scheduled_at phase.

## 16:47 HKT — Time and Job certificates

### Reusable imported Nat isomorphism

`rocq/ImportedNatBridge.v` defines structural conversions between Rocq `nat`
and the actual imported Lean `Nat`, plus both round trips:

```text
imported_nat_to_rocq (rocq_nat_to_imported n) = n
rocq_nat_to_imported (imported_nat_to_rocq nL) = nL
```

The first equality is Rocq equality; the second is imported Lean equality in
`SProp`. Both proofs passed. `Print Assumptions` reports the first as closed
under the global context and the second as depending only on the importer's
definitional UIP for imported equality.

### Actual declaration results

`rocq/TimeJobCertificates.v` directly names all six actual imported
declarations. It supplies bidirectional isomorphisms for the three aliases and
canonical record mappings for the three Job classes. For example,
`import_job_cost` maps an original `JobCost` record to the actual imported Lean
`JobCost` record by applying the Nat conversion to its field; the certificate
then proves that the actual imported `job_cost` projection commutes. No
unconstrained projection-correspondence hypothesis is used.

Compilation exited 0. The complete output is
`reports/logs/time_job_certificates.log`; every `Print Assumptions` invocation
reports only imported equality's definitional UIP.

| Target | Imported? | Source identified? | Semantic relation | Own proof | Closure | Mutation | Status |
| --- | --- | --- | --- | --- | --- | --- | --- |
| `instant` | yes | Prosa v0.6 `behavior/time.v` | explicit Rocq-nat/imported-Nat isomorphism | pass, two round trips | closed | not meaningful for transparent type alias | **CERTIFIED** |
| `duration` | yes | same | same Nat isomorphism | pass, two round trips | closed | not meaningful | **CERTIFIED** |
| `work` | yes | Prosa v0.6 `behavior/job.v` | same Nat isomorphism | pass, two round trips | closed | not meaningful | **CERTIFIED** |
| `JobCost.job_cost` | yes | same | canonical class-record mapping + `ImportedNatRel` | pass | closed for every source instance under the canonical mapping | not yet run | **PARAMETRICALLY_CERTIFIED** |
| `JobArrival.job_arrival` | yes | same | canonical class-record mapping + `ImportedNatRel` | pass | same | not yet run | **PARAMETRICALLY_CERTIFIED** |
| `JobDeadline.job_deadline` | yes | same | canonical class-record mapping + `ImportedNatRel` | pass | same | not yet run | **PARAMETRICALLY_CERTIFIED** |

The `eqType → Type + DecidableEq` representation change is explicit: the Job
carrier is shared by the canonical mapping, while observable equality is
handled by `EqTypeBridge.v`. No claim that the two typeclass packages are
structurally equal is made.

Reusable bridge coverage after this stage:

- imported Nat isomorphism: 6 certified declarations now, and it is a direct
  dependency for all arrival-time/order targets;
- canonical single-field record/projection mapping pattern: 3 Job projections;
- eqType equality bridge: Ideal scheduling now, future arrival membership.

## 17:02 HKT — reusable seq/List and membership bridge

`rocq/ImportedListBridge.v` now provides:

- structural conversion between MathComp `seq` (Rocq list) and actual
  imported Lean `List_inst1`;
- both list round trips;
- `ImportedListRel`;
- `ImportedBoolSPropRel`, the explicit relation between a MathComp boolean
  predicate and an imported Lean `SProp` predicate;
- a structural two-way membership proof between `j \in xs` and actual imported
  `List_Mem_inst1 j (seq_to_imported_list xs)`.

The backward membership proof first decodes the imported list and then
transports the boolean truth along the proved list round trip. This avoids any
forbidden elimination of an imported `SProp` witness into Rocq `Prop`.

Compilation exited 0. `Print Assumptions` reports:

- source list round trip: closed under the global context;
- imported list round trip: only imported equality's definitional UIP;
- membership bridge: only the local imported truth representation's
  definitional UIP.

The exact output is `reports/logs/imported_list_bridge.log`.

**Machine-checked reusable bridge:** MathComp `seq` ↔ imported Lean List,
including membership, **PASS**. Immediate downstream targets are
`arrival_sequence`, `arrivals_at`, and `arrives_at`; the same bridge is the
base for later Nodup and concatenation work.

## 17:07 HKT — first three Arrival_sequence targets

`rocq/ArrivalSequenceCertificates.v` defines a canonical representation map
from an original arrival sequence to the actual imported Lean function:

```text
tL ↦ seq_to_imported_list (arrR (imported_nat_to_rocq tL))
```

It then proves the actual declarations compositionally:

| Target | Imported? | Relation | Dependencies | Proof | Assumptions | Status |
| --- | --- | --- | --- | --- | --- | --- |
| `arrival_sequence` | yes | pointwise related instant → `ImportedListRel` | Nat and List isomorphisms | pass | imported equality UIP only | **PARAMETRICALLY_CERTIFIED** |
| `arrivals_at` | yes | `ImportedListRel` | preceding pointwise function certificate | pass | imported equality UIP only | **PARAMETRICALLY_CERTIFIED** |
| `arrives_at` | yes | `ImportedBoolSPropRel` | arrivals_at + structural membership bridge | pass | imported equality/local STrue UIP only | **PARAMETRICALLY_CERTIFIED** |

These statuses are “parametric” only because an arrival sequence is an input
function over an arbitrary `Job : eqType`; no target-specific semantic premise
is assumed. The canonical mapping and all dependency bridges are proved.

The Rocq command exited 0. Full output:
`reports/logs/arrival_sequence_certificates.log`. Mutation tests are not yet
run for these projection/wrapper-level declarations.

## 17:18 HKT — Nat order and arrival-time predicates

`rocq/ImportedNatOrderBridge.v` structurally proves two-way correspondence for
MathComp boolean `leq`/`ltn` and the actual imported Lean `Nat_le`/`Nat_lt`.
It also proves a reusable composition rule from boolean conjunction to
imported Lean `And` in `SProp`. No appeal to MathComp/Mathlib global
isomorphism is made.

`rocq/ArrivalTimeCertificates.v` then unfolds and certifies the actual
imported declarations using the canonical `JobArrival` record mapping:

| Target | Imported? | Relation | Dependencies | Proof | Assumptions | Status |
| --- | --- | --- | --- | --- | --- | --- |
| `has_arrived` | yes | MathComp boolean ≤ ↔ imported `Nat_le` | Nat isomorphism, JobArrival projection, order bridge | pass | local STrue UIP only | **PARAMETRICALLY_CERTIFIED** |
| `arrived_before` | yes | MathComp boolean < ↔ imported `Nat_lt` | same | pass | same | **PARAMETRICALLY_CERTIFIED** |
| `arrived_between` | yes | boolean conjunction ↔ imported `And` | two order bridges + conjunction composition | pass | same | **PARAMETRICALLY_CERTIFIED** |

Both Rocq compilation commands exited 0. Logs:

- `reports/logs/imported_nat_order_bridge.log`;
- `reports/logs/arrival_time_certificates.log`.

The order bridge now covers three downstream declarations and is reusable for
range/interval proofs later in this phase.

## 17:24 HKT — proposition-sort boundary audit

The actual artifacts for `arrives_in`, `consistent_arrival_times`,
`arrival_sequence_uniq`, and `valid_arrival_sequence` are imported and their
source declarations are identified. A full bidirectional certificate is
currently blocked by the legacy importer's use of Lean `SProp`:

- original `arrives_in` uses Rocq `Prop` existential;
- imported `arrives_in` uses witness-carrying `SProp` `Exists`;
- the validity declarations similarly quantify in ordinary Rocq `Prop` but
  their imported counterparts quantify in `SProp` and depend on imported
  membership/Nodup witnesses.

`rocq/SPropBoundaryAudit.v` makes this a kernel-checked negative finding. Two
`Fail Definition` commands verify that Rocq rejects both elimination of a
Rocq `Prop` existential into imported `SProp Exists` and elimination of an
imported witness-carrying `SProp Exists` into a Rocq `Prop` existential. The
audit file itself compiles with exit code 0 only because both forbidden
definitions are rejected. Empty `SProp` elimination is allowed and is not the
problem.

| Target | Actual imported? | Source identified? | Dependency state | Status |
| --- | --- | --- | --- | --- |
| `arrives_in` | yes | yes | Nat/List/membership certified; existential sort bridge unavailable | **BLOCKED** |
| `consistent_arrival_times` | yes | yes | equality/time bridges certified; full two-way membership implication crosses the same sort boundary | **BLOCKED** |
| `arrival_sequence_uniq` | yes | yes | structural List bridge certified; declaration-level Prop/SProp forall bridge unavailable | **BLOCKED** |
| `valid_arrival_sequence` | yes | yes | both constituent declaration certificates blocked | **BLOCKED** |

These are not marked `FAILED`: no semantic mismatch was found. No axiom or
weakened one-way statement is introduced. Log:
`reports/logs/sprop_boundary_audit.log`.
