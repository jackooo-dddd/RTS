# Prosa 0.6 Rocq→Lean semantic-validation pilot

Last updated: 2026-09-17 (Asia/Hong_Kong)

## Status summary

This report is an append-oriented experiment log. Facts labeled **verified**
were established by the named tool command. Judgments labeled **analysis** are
not semantic certificates.

| Target | Actual Lean imported? | Own proof | Dependency closure | Assumptions clean | Mutation rejected | Status |
| --- | --- | --- | --- | --- | --- | --- |
| `scheduled_in` | no (import stops in a transitive Lean/Mathlib dependency) | conditional bridge scaffolding passes Rocq | no | yes for scaffolding only | fixture pass; end-to-end N/A | **BLOCKED** |
| `completed_by` | no (same importer blocker) | conditional compositional bridge passes Rocq | no (`service` bridge cannot be tied to the actual Lean artifact) | yes for scaffolding only | fixture pass; end-to-end N/A | **BLOCKED** |

No target is `CERTIFIED`. The required proposition mentioning the actual
imported Lean declaration has not been accepted by the Rocq kernel.

## Stage 1 — repository and provenance inventory

### Verified facts

- The requested workspace was initially empty and was populated with
  `git clone https://github.com/jackooo-dddd/RTS.git .`.
- RTS commit under validation:
  `845f156a6a75f704361c230870d97566a14b6913`.
- The checkout has one visible commit, no tags, no submodules, no `lakefile`,
  no `lean-toolchain`, and no bundled `rt-proofs` source.
- Modern targets are exactly:
  - `Prosa-fei/Prosa/Behavior/Schedule.lean`, declaration
    `Prosa.Behavior.Schedule.ProcessorState.scheduled_in`;
  - `Prosa-fei/Prosa/Behavior/Service.lean`, declaration
    `Prosa.Behavior.Service.completed_by`.
- `Classic/` was not modified or used.
- Both Lean files say they were translated from
  `../rt-proofs/behavior/{schedule,service}.v`.
- An existing opam switch named `prosa-0.6` contains `rocq-prosa.0.6` and the
  installed exact source files under
  `~/.opam/prosa-0.6/lib/coq/user-contrib/prosa/behavior/`.
- The opam package pins the upstream archive tag `v0.6`; read-only remote tag
  resolution established:
  - tag object: `dd12237d8f8d503d465019f9b58b67ebadd4950e`;
  - peeled commit: `414e66760333eaa4ef78c685bcf53291c527a548`.
- Package archive checksum from opam metadata:
  `sha512=128dd213e687653a6ad5a55f33e76d39f4301f4fb22ff2c58379bb9d727ada00da776beee213e89b6be117f4db7c7bd73e467e28f57dfbee017891a4121e6228`.
- Installed source SHA-256 values:
  - `schedule.v`: `4e5f3cdf60fe6d7cf8872345f64a3126ea500f34618ca322e4d754d9b626e50d`;
  - `service.v`: `3fd8cf88d667d3c43fae1a7ec62a89f6cef75fcd8e622a59f5a747153c1c4870`;
  - `job.v`: `f107dc6095d152bdf8b7eeb030b73ba47967cee67806991ed7efe24407a5a752`;
  - `time.v`: `9fea3f9a3181ca697e8abdb9eee90a656057081f62b00157c3ce9fbe59e53230`.

### Tool versions and availability

- Lean: `4.33.1`, commit
  `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`.
- Lake: `5.0.0-src+819816b`.
- Mathlib tag: `v4.33.1`, commit
  `0df444a360eaa60ab8c11dca51a86af692955474`.
- Rocq in the Prosa switch: `9.0.1` (OCaml `4.14.2`).
- Installed MathComp: `2.4.0`; installed `rocq-prosa`: `0.6`.
- opam: `2.5.2`.
- `lean4export` and `rocq-lean-import` were not initially installed as commands.
  Both were built from source during this pilot.

## Stage 2 — source comparison and representation findings

### `scheduled_in`

Rocq v0.6 defines:

```coq
Definition scheduled_in (j : Job) (s : State) : bool :=
  [exists c : Core, scheduled_on j s c].
```

The actual Lean declaration defines `decide (∃ c, scheduled_on j s c = true)`
using its `Fintype Core` and `DecidableEq Core` fields. At the observable level,
these definitions have the intended same existential semantics provided that
the two core enumerations correspond and `scheduled_on` is preserved.

### `completed_by`

Both source-level target definitions express cumulative service greater than
or equal to job cost. However, a significant upstream-interface mismatch was
found below the target:

- Rocq v0.6 `ProcessorState` has per-core `supply_on` and `service_on`, laws
  connecting them, and *derives* `service_in` by summing `service_on` over all
  cores.
- The Lean translation drops `supply_on`, per-core `service_on`, and the
  service/supply bound. It instead stores an aggregate `service_in` directly,
  constrained only by `service_implies_scheduled`.

Therefore `completed_by` is not dependency-closed under a structural record
isomorphism. A valid certificate needs an explicit refinement relation whose
observable condition states that Lean `service_in` equals the Rocq per-core
sum. This condition is semantically necessary; without it, Lean instances can
choose arbitrary aggregate service and change completion results.

### Job equality warning

Rocq `JobType := eqType`. Lean has only `abbrev JobType := Type`, despite the
comment claiming decidable equality. The Lean `ProcessorState` class does not
require `[DecidableEq Job]`. This target does not itself compare jobs—the
observable equality behavior is hidden inside `scheduled_on`—so the pilot
bridge must preserve that observable instead of asserting `eqType ≅ Type`.
For later definitions that directly compare jobs, an explicit related
`DecidableEq` instance will be required.

## Stage 3 — actual Lean build and export

### Verified result: build PASS

The original files were not edited. Using Lean 4.33.1 and Mathlib v4.33.1,
temporary `.olean` files were built outside the repository for:

1. `Prosa.Behavior.Time`;
2. `Prosa.Behavior.Job`;
3. `Prosa.Util.Notation`;
4. `Prosa.Behavior.Arrival_sequence`;
5. `Prosa.Behavior.Schedule`;
6. `Prosa.Behavior.Service`.

Both target files compiled successfully.

### Verified result: lean4export PASS

Two exporter variants were tested:

- current format 3.1 NDJSON, using `lean4export` commit
  `15f6055e299ad5b89345e533cc2192f4cc00f659` built with Lean 4.33.1;
- legacy-format exporter commit
  `c9f8373f8a37a65c0ed9bfd20480a3d7481a163e`, also built with the actual
  Lean 4.33.1 toolchain.

Artifacts created from the actual compiled modules:

- `export/ProsaPilot.ndjson`: 190,902 lines, 9,927,641 bytes; metadata names
  Lean 4.33.1 and exporter format 3.1.0.
- `export/ProsaPilot.out`: legacy stream containing both targets.
- `export/ScheduledIn.out`: 117,742 lines, 2,598,107 bytes.
- `export/CompletedBy.out`: 180,660 lines, 4,155,512 bytes.

This proves that actual Lean artifacts were exported. It does **not** prove
that Rocq imported or semantically related them.

## Stage 4 — Rocq import attempts

### Route A: Rocq 9.0.1 plus legacy importer

`rocq-lean-import` tag `v0.0.2` required small source-compatibility patches to
build against Rocq 9.0.1. Import then failed almost immediately on imported
Lean `Equivalence` with a Rocq kernel assertion in `kernel/typeops.ml`.

Result: **FAILED**. No target declaration was imported.

### Route B: Rocq 9.2.0 plus importer v0.0.2

A separate opam switch (`validation-rocq-9.3`, despite the name presently
containing Rocq 9.2.0) was created. The repository available to opam exposed
Rocq versions only through 9.2.0, whereas current `rocq-lean-import` requires
Rocq ≥9.3.

The older importer tag `v0.0.2` builds cleanly on Rocq 9.2.0. Import of the
legacy stream progressed through 1,143 entries but stopped at line 70,220:

```text
Error at line 70220 (for Lean.Omega.IntList.dot_sdiv_left):
cannot project non record Inhabited
```

The same failure occurs for the split `ScheduledIn.out`, before the target
declaration. The combined file and `CompletedBy.out` therefore cannot yield
usable target declarations either.

Result: **PIPELINE BLOCKED — ACTUAL LEAN ARTIFACT NOT IMPORTED**.

An experimental attempt to backport the upstream dependent-projection fix is
in progress only in `/private/tmp`; it has not altered this repository and is
not part of the claimed validator.

## Stage 5 — bridge scaffolding

Files written:

- `rocq/Relations.v`: `BoolRel`, Bool-to-Prop relation, `NatRel`, `FunRel`,
  and `PredRel`.
- `rocq/NatBridge.v`: natural-order bridge from constituent `NatRel`s.
- `rocq/BoolBridge.v`: basic boolean relation lemmas.
- `rocq/FiniteBridge.v`: minimal finite-existential bridge using a pair of
  inverse core maps and pointwise predicate preservation.
- `rocq/ProcessorStateBridge.v`: applies the finite bridge to the *actual Rocq*
  `scheduled_in` and a Lean-shaped observable model.
- `rocq/CompletedByCertificate.v`: compositional bridge from actual Rocq
  `completed_by` to a Lean-shaped model, parameterized by explicitly
  uncertified `service` and `job_cost` relations.
- `rocq/MutationFixtures.v`: finite counterexamples for exists→forall,
  predicate polarity, ≥→≤, and ≥→> mutations.

These are scaffolding because the Lean-shaped side is not the imported Lean
declaration. Rocq accepts them, but their maximum status is `CONDITIONAL`.

## Dependency graph

```text
scheduled_in
├── Job relation / observable scheduled_on preservation [CONDITIONAL]
├── State relation [CONDITIONAL]
├── Core finite enumeration bijection [bridge written]
├── scheduled_on Bool relation [CONDITIONAL]
└── Lean declaration import [BLOCKED]

completed_by
├── Job relation [CONDITIONAL]
├── instant/work Nat relation [bridge written]
├── schedule/state relation [CONDITIONAL]
├── Rocq service_in = sum per-core service_on [source definition]
├── Lean aggregate service_in refinement [UNCERTIFIED]
├── service_at [depends on aggregate refinement]
├── service_during / finite interval sum [UNCERTIFIED]
├── service [UNCERTIFIED]
├── job_cost [CONDITIONAL]
├── Nat ≤ [bridge written]
└── Lean declaration import [BLOCKED]
```

## Assumption audit

The full output is in `reports/assumptions.log`. Rocq printed
`Closed under the global context` for all nine audited scaffolding and mutation
lemmas. No target certificate exists, so there is still no successful actual-
artifact target assumption closure to report.

## Mutation testing

No successful actual-artifact certificate exists, so mutation rejection for
the requested end-to-end validator is **N/A**. Four kernel-checkable fixtures
pass and demonstrate that the bridge semantics distinguish exists from forall,
predicate polarity, ≥ from ≤, and ≥ from >. These are fixture-level `PASS`
results, not mutation tests of an imported Lean declaration.

## Stage 6 — Rocq bridge verification log

Verified with Rocq 9.0.1 in the `prosa-0.6` opam switch:

```text
Relations.v                     PASS
NatBridge.v                     PASS
BoolBridge.v                    PASS
FiniteBridge.v                  PASS
ProcessorStateBridge.v          PASS
CompletedByCertificate.v        PASS (conditional/model-side only)
MutationFixtures.v              PASS
AssumptionAudit.v               PASS
```

`Print Assumptions` results:

```text
nat_le_bridge                             Closed under the global context
nat_ge_bool_prop_bridge                   Closed under the global context
finite_exists_bridge                      Closed under the global context
scheduled_in_observable_bridge            Closed under the global context
completed_by_compositional_bridge         Closed under the global context
scheduled_exists_forall_mutation_detected Closed under the global context
scheduled_polarity_mutation_detected      Closed under the global context
completed_ge_le_mutation_detected         Closed under the global context
completed_ge_gt_mutation_detected         Closed under the global context
```

The compositional `completed_by` proof uses only the certified Nat-order
bridge plus explicit `service_rel` and `cost_rel` premises. Those premises are
recorded as uncertified dependencies because the imported Lean functions are
unavailable. There are no `Admitted`, arbitrary `Axiom`, or Rocq opaque escape
hatches in the validation sources.

## Translation modification

The existing Lean translation has not been modified. All repository changes
are under `Prosa-fei/Validation/`.

## Commands run (representative)

```sh
git clone https://github.com/jackooo-dddd/RTS.git .
git rev-parse HEAD
lean --version
opam exec --switch=prosa-0.6 -- rocq --version
git ls-remote https://gitlab.mpi-sws.org/RT-PROOFS/rt-proofs.git refs/tags/v0.6 'refs/tags/v0.6^{}'
git clone --depth 1 --branch v4.33.1 https://github.com/leanprover-community/mathlib4.git /private/tmp/mathlib4-v4.33.1
cd /private/tmp/mathlib4-v4.33.1 && lake exe cache get
# lean -R ... -o /private/tmp/prosa-olean/... for each target dependency
# lean4export ... -- Prosa.Behavior.Schedule.ProcessorState.scheduled_in
# lean4export ... -- Prosa.Behavior.Service.completed_by
opam exec --switch=prosa-0.6 -- rocq c ... Imported.v
opam switch create validation-rocq-9.3 ocaml-base-compiler.4.14.2 -y
opam install --switch=validation-rocq-9.3 -y rocq-core.9.2.0 rocq-stdlib yojson
opam exec --switch=validation-rocq-9.3 -- rocq c ... ImportedScheduled.v
```

Reproducible scripts are provided under `scripts/`. `export_lean.sh` requires
explicit paths to the pinned Mathlib checkout and exporter binary;
`import_lean.sh` requires an explicit built importer tree and opam switch.

## Current blocker and next minimal step

The blocker is tooling, not a completed negative semantic result: the actual
Lean declarations export successfully, but the available Rocq/importer pair
does not finish importing their transitive Mathlib closure.

The next minimal bridge/tool step is to run current `rocq-lean-import` with
Rocq ≥9.3 (which includes the dependent-projection fixes), or complete a small
backport of those fixes to the Rocq 9.2-compatible importer. Once import works,
the first target should connect the imported finite existential to
`FiniteBridge.v`; `completed_by` should then proceed only after proving the
aggregate-service refinement through the interval sum.

## Stage 7 — final local integrity check

The final `scripts/verify.sh` run completed with exit code 0 and printed:

```text
Bridge scaffolding: PASS
Actual-artifact certificates: BLOCKED (run import_lean.sh for the recorded failure)
```

`git diff --check` passed. A scan of the Rocq validation sources found no
`Admitted`, `Axiom`, or `sorry`. Generated Rocq `.vo`, `.vos`, `.vok`, `.glob`,
and `.aux` files were removed after verification. `git status --short` shows
only the new `Prosa-fei/Validation/` tree; the existing translation, including
`Classic/`, remains unchanged.

### Research-question answer at this stage

This pilot does not yet demonstrate that existing automatically translated
Prosa 0.6 definitions can be semantically certified directly. It demonstrates
three narrower facts:

1. the unmodified target Lean files build and their real declarations can be
   exported;
2. the minimal mathematical bridges for finite existential and completion
   order are Rocq-kernel checked without assumptions;
3. the end-to-end certificate is blocked at Lean-artifact import, and
   `completed_by` additionally requires an explicit aggregate-service
   refinement because the translated processor-state abstraction differs from
   Rocq v0.6.

Hence the technically honest outcome is a combination of **B** (explicit
representation relations are necessary) and **E** (the available importer
toolchain prevents actual Lean import), not a semantic PASS or a demonstrated
target-level mismatch.

## Stage 8 — bounded importer backport experiment

After the Stage 7 snapshot, a minimal experimental patch was applied only to
the temporary `/private/tmp/rocq-lean-import` checkout. It unfolds projections
on non-record single-constructor inductives as `case` expressions and computes
the result relevance from the projected field type. This removed the earlier
`Lean.Omega.IntList.dot_sdiv_left` / `Inhabited` failure.

The split `scheduled_in` import then progressed from 1,143 to 1,394 imported
entries and failed later at legacy-export line 90,537:

```text
Error at line 90537 (for UInt32.toBitVec): #DEF 9187 79903 79905
The term "fun self : UInt32 => Lean.val0 self" has type
 "UInt32 -> Fin UInt32_size"
while it is expected to have type
 "UInt32 -> BitVec (OfNat_ofNat_inst1 Nat 32 (instOfNatNat 32))".
```

The complete latest attempt is saved in `reports/import_scheduled.log`.
This is evidence that the first projection blocker was repairable, but the
actual target is still not imported. The new failure is a conversion mismatch
between the predeclared `UInt32` projection and Lean's `BitVec 32` alias. No
temporary importer patch is included in the repository or counted as a
certificate dependency.
