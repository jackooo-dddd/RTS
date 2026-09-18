# Prosa 0.6 Rocq→Lean semantic-validation pilot

> **2026-09-18 continuation:** the import blocker recorded below was resolved.
> The unchanged actual `ScheduledIn.out` now imports fully, and Rocq 9.3
> accepts a direct actual-artifact `scheduled_in` correspondence theorem plus
> its mutation-rejection fixture. The honest status is **CONDITIONAL**, because
> the explicit core mapping and `scheduled_on` preservation premises are not
> yet instantiated. See
> `import_experiment_2026-09-18_0813_HKT.md` for the complete append-only
> continuation, exact patches, logs, assumption audit, hashes, and commands.
> The older BLOCKED table below is retained as the prior experiment snapshot.

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

The full output is in `reports/logs/assumptions.log`. Rocq printed
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

The complete latest attempt is saved in `reports/logs/import_scheduled.log`.
This is evidence that the first projection blocker was repairable, but the
actual target is still not imported. The new failure is a conversion mismatch
between the predeclared `UInt32` projection and Lean's `BitVec 32` alias. No
temporary importer patch is included in the repository or counted as a
certificate dependency.

## Stage 9 — import-only recovery task started

Per user direction, all new semantic-bridge work and expansion to other Prosa
files is paused. The only active objective is to import
`export/ScheduledIn.out` completely and make the actual imported Lean
`Prosa.Behavior.Schedule.ProcessorState.scheduled_in` referenceable in Rocq.

Starting state:

- current repository certificate status remains `BLOCKED`;
- Rocq 9.2 plus the temporary minimal projection/relevance backport reaches
  `UInt32.toBitVec` at legacy-export line 90,537;
- the preferred next attempt is an unmodified current `rocq-lean-import` with
  Rocq ≥9.3;
- `ProcessorStateBridge.v` will not be changed unless and until the real Lean
  declaration imports successfully.

### Stage 9.1 — current upstream version resolution

Read-only upstream resolution on 2026-09-17 established:

- current `rocq-lean-import` master:
  `546979bfd55b94288abfb72583a534b0136d282d`;
- its opam metadata requires `rocq-core >= 9.3~`;
- the newest available Rocq 9.3 tag is the release candidate `V9.3+rc1`,
  peeled commit `67e678adcd0cb911fec4eca313d9843492881956`;
- the synchronized public opam repository still lists `rocq-core` only through
  9.2.0.

Accordingly, the preferred-path attempt will build the exact Rocq 9.3 RC1 tag
in a separate switch and use the unmodified importer master. This is isolated
tooling work; no bridge or Prosa source is being changed.

### Stage 9.2 — Rocq 9.3 RC1 core built; released stdlib is incompatible

An isolated opam switch `rocq93rc1` (OCaml 4.14.2) was created. The exact
Rocq `V9.3+rc1` source checkout at
`67e678adcd0cb911fec4eca313d9843492881956` was pinned as
`rocq-runtime.dev` and `rocq-core.dev`; both packages built and installed
successfully.

Installing the newest stdlib package available from the synchronized public
opam repository (`rocq-stdlib.9.1.0`) failed against this core. Compilation
reached `Zmod/ZstarBase.v:198` and Rocq reported:

```text
Error: Multiple "Proof" commands not supported.
```

This is a source-version incompatibility between the 9.1 stdlib package and
the 9.3 RC1 proof engine, not an error in `ScheduledIn.out`. The next import
step is therefore blocked on selecting and building the stdlib revision that
matches Rocq 9.3 RC1. No repository source or bridge was modified by this
attempt; the failed package build exists only inside the isolated opam switch.

Commands used in this stage included:

```text
opam switch create rocq93rc1 ocaml-base-compiler.4.14.2 -y
opam pin add --switch=rocq93rc1 rocq-runtime.dev /private/tmp/rocq-9.3-rc1 -y
opam pin add --switch=rocq93rc1 rocq-core.dev /private/tmp/rocq-9.3-rc1 -y
opam install --switch=rocq93rc1 rocq-stdlib.9.1.0 -y
```

### Stage 9.3 — exact Rocq 9.3 RC1 stdlib installed

The Rocq 9.3 RC1 source tree records its stdlib CI dependency in
`dev/ci/ci-basic-overlay.sh` as commit
`b89635f66d5d5fe3c91a5755b389a30846411888`. That exact stdlib revision was
checked out at `/private/tmp/rocq-stdlib-93`, pinned as `rocq-stdlib.dev`, and
built successfully in switch `rocq93rc1`. The installed core now reports:

```text
The Rocq Prover, version 9.3+rc1
compiled with OCaml 4.14.2
```

The switch contains matching pinned `rocq-runtime.dev`, `rocq-core.dev`, and
`rocq-stdlib.dev`. This resolves the Stage 9.2 stdlib blocker. No validation
repository or bridge source was modified; all pins point to exact temporary
source checkouts. The next step is to build unmodified
`rocq-lean-import` master and test the existing legacy export.

### Stage 9.4 — importer master exposes a post-RC1 API dependency

A clean checkout of current `rocq-lean-import` master at
`546979bfd55b94288abfb72583a534b0136d282d` was created at
`/private/tmp/rocq-lean-import-current` and built unmodified in `rocq93rc1`.
The build failed before any import at `src/lean.ml:305`:

```text
let sets : Level.t Int.Map.t Summary.Ref.t =
                                   ^^^^^^^^^^^^^
Error: Unbound module Summary.Ref
```

Thus the current importer source uses a Rocq API newer than the exact 9.3 RC1
tag even though its opam constraint says `rocq-core >= 9.3~ | = dev`. This is
a tool-version blocker, not a `ScheduledIn.out` failure. The checkout remains
clean and no importer patch has yet been applied. The next action is to inspect
importer history for the newest revision that both contains the relevant
dependent-projection/`UInt32.toBitVec` work and builds with 9.3 RC1; if none
exists, use a minimal compatibility patch or a newer Rocq development commit.

### Stage 9.5 — master plus RC1 compatibility reaches `UInt32.toBitVec`

The unmodified importer master was made buildable on 9.3 RC1 with one
temporary compatibility patch: the `Summary.Ref` API migration from importer
commit `237f9ac` was reversed locally, restoring the ordinary `ref` type and
operators returned by `Summary.ref`. This changes only importer bookkeeping
syntax; it does not change expression translation. The patched importer built
successfully.

Importing the unchanged `export/ScheduledIn.out` then successfully passed the
previous dependent-projection failure at line 70,220. In particular,
`Lean.Omega.IntList.dot_sdiv_left` and the projected
`Nonempty_inst1.(field).val1` were accepted. The run stopped at 1,394 imported
entries, legacy-export line 90,537, on the already isolated UInt32 mismatch:

```text
Error at line 90537 (for UInt32.toBitVec): #DEF 9187 79903 79905
The term "fun self : UInt32 => Lean.val0 self" has type
 "UInt32 -> Fin UInt32_size"
while it is expected to have type
 "UInt32 -> BitVec (OfNat_ofNat_inst1 Nat 32 (instOfNatNat 32))".
```

The full run is recorded in
`reports/logs/import_scheduled_rocq93_master.log`. This confirms with Rocq 9.3 RC1
that importer master contains the required dependent-projection repair, but
master does not contain upstream branch commit
`fc148dfa2e8f27e1a9753e9403d26f0d16440279` (`add support for UInt32`). That
commit is currently present only on upstream branch `fix-UInt32`. The next
attempt will add that exact upstream patch to the temporary importer checkout,
on top of the RC1 compatibility patch. The actual Lean artifact and validation
bridges remain unchanged.

### Stage 9.6 — upstream UInt32 patch works; next blocker is `String.mk`

The exact functional changes from upstream branch commit
`fc148dfa2e8f27e1a9753e9403d26f0d16440279` were applied to the temporary
importer checkout. They predeclare Lean `BitVec`, represent `UInt32` through
its actual `toBitVec : BitVec 32` field, and predeclare the required `Nat.add`,
`Nat.mul`, and `Nat.pow` operations. Together with the RC1 compatibility
change, the importer and its Rocq support file built successfully.

The next import passed `UInt32.toBitVec` and continued through
`UInt32.toNat`, `Char`, UTF-8 helpers, and the imported `String` declaration.
It stopped at legacy-export line 91,687:

```text
Error at line 91687 (for String.instInhabited): #DEF 9457 80738 80742
missing String.mk
```

The run reached 1,437 imported entries and is saved in
`reports/logs/import_scheduled_rocq93_uint32.log`. Therefore the upstream UInt32
patch is empirically sufficient for the earlier UInt32 blocker; it is still a
temporary importer-only patch and is not part of the RTS repository. The new
blocker is resolution of Lean 4.33's `String.mk` constructor after the
predeclared/imported `String` representation. No semantic bridge or translated
Prosa source has been changed.

### Stage 9.7 — Lean 4.33 string literals imported; native crash is next blocker

A temporary importer adaptation now constructs a Lean 4.33 string literal
compositionally using the already imported actual declarations:

```text
List.utf8Encode
ByteArray.IsValidUTF8.intro
Eq.refl
String.ofByteArray
```

The literal's character list is UTF-8 encoded, and the validity witness is a
kernel term `ByteArray.IsValidUTF8.intro chars eq_refl`; no axiom or admitted
proof is introduced. The importer first failed to compile because the equality
universe was supplied in the importer's internal representation; changing it
to the legacy-export universe `LeanExpr.U.Succ LeanExpr.U.Prop` fixed that
local issue, and the importer built successfully.

The unchanged `ScheduledIn.out` import then accepted `String.instInhabited`,
all subsequent string literals observed in this section, `String.ofList`, and
continued past line 91,901. It next terminated with native signal 11 while
processing immediately after:

```text
line 91990: _private.Init.Prelude0.isValidChar_UInt32.match_1_1
Segmentation fault: 11
```

The run is saved in `reports/logs/import_scheduled_rocq93_string.log`. Unlike the
previous failures, Rocq emitted no ordinary kernel error and no `Done!`
summary, so this stage is still a failed import. The next task is to isolate
the crashing declaration with `Lean Import ... From ... Until ...` bounds and
obtain a native backtrace or a minimal importer-side cause. The string patch is
temporary and only in `/private/tmp/rocq-lean-import-current`; no bridge or
Prosa translation file has been changed.

### Stage 9.8 — crash boundary isolated exactly

The importer command accepts optional numeric `from`/`until` bounds. A bounded
kernel import through (but excluding) legacy line 91,990 was run as:

```text
Lean Import "/absolute/path/to/ScheduledIn.out" 0 91990.
```

That bounded import completed successfully and produced a 3.0 MB Rocq `.vo`
with this summary:

```text
Done!
- 1449 entries (2350 possible instances) (including quot).
- 50 universe expressions
- 9535 names
- 80957 expression nodes
Max universe instance length 5.
0 inductives have non syntactically arity types.
```

Consequently the signal-11 boundary is the declaration beginning at line
91,990 itself, `_private.Init.Prelude0.isValidChar_UInt32.match_1_1`, rather
than an earlier corrupted string import. This declaration ends at `#DEF 9519`
and is a large dependent match used by the UInt32 character-validity path.
The artifact still has not fully imported. Because current importer master also
targets a post-RC1 `Summary.Ref` API, the preferred next experiment is current
Rocq development head plus its matching stdlib, removing the RC1 compatibility
patch and checking whether the native crash is already fixed in Rocq core.

### Stage 9.9 — current Rocq development environment built

The preferred current-head environment was resolved and built from exact
revisions:

- Rocq master `03e4ab26b741f23cd1e136bc471a222067c08c09`
  (`9.4+alpha`, 2026-09-17);
- stdlib master `1593d617cc9496e10be236cda9070d0380c4b252`, as selected
  by that Rocq tree's CI overlay;
- importer master remains
  `546979bfd55b94288abfb72583a534b0136d282d`.

They are installed in isolated switch `rocq-master` with OCaml 4.14.2. The
importer was restored to its native current `Summary.Ref` implementation, so
the RC1 compatibility reversal is no longer present in this build. Only the
upstream `fix-UInt32` functional changes and the temporary Lean 4.33 string
literal adaptation remain. After regenerating the Rocq makefile and cleaning
objects compiled under RC1, this importer built successfully against current
Rocq. The next command is a full import of the unchanged `ScheduledIn.out` to
test the declaration isolated in Stage 9.8.

### Stage 9.10 — current Rocq reproduces the same native crash

The complete import was rerun with current Rocq master, current matching
stdlib, importer master plus only the UInt32/string functional fixes, and the
unchanged `ScheduledIn.out`. It again terminated with signal 11 immediately
after printing exactly:

```text
line 91990: _private.Init.Prelude0.isValidChar_UInt32.match_1_1
Segmentation fault: 11
```

The current-head log is
`reports/logs/import_scheduled_rocq_master.log`. This rules out the exact 9.3 RC1
revision as the sole cause and shows the crash is reproducible on Rocq master
`03e4ab26...`. Since the crashing term is a deeply nested dependent match and
no kernel diagnostic is printed, the next minimal non-semantic experiment is
to raise the native process stack limit and rerun. No declaration will be
skipped: a skip-based import would not count as successful dependency-closed
actual-artifact import.

### Stage 9.11 — larger native stack advances past the isolated declaration

The default macOS stack limit was 8,176 KB; its hard limit is 65,520 KB. A
full current-head import with the stack raised to 65,520 KB accepted the
previously crashing declaration and advanced through:

```text
line 91990: _private.Init.Prelude0.isValidChar_UInt32.match_1_1
line 92040: _private.Init.Prelude0.isValidChar_UInt32
line 92047: Char.ofNatAux._private_1
line 92064: Char.ofNatAux
```

It then again terminated with signal 11 while entering the still deeper
`Char.ofNat` proof immediately following line 92,064. The log is
`reports/logs/import_scheduled_rocq_master_stack64m.log`. This is strong operational
evidence of native stack exhaustion in the recursive expression conversion,
not a Rocq kernel rejection: increasing the stack moved the failure boundary
forward across the exact declaration that failed at 8 MB. The platform hard
limit prevents raising the OCaml 4 native stack further. The next minimal
attempt is the same current Rocq/importer sources under OCaml 5, whose runtime
uses dynamically managed stacks, before considering an invasive iterative
rewrite of importer expression conversion.

### Stage 9.12 — OCaml 5 avoids the crash but exposes legacy-opacity cost

The same current Rocq and stdlib were built under OCaml 5.2.1 in switch
`rocq-master-ocaml5`, and the importer built successfully. The full import no
longer crashed at `Char.ofNatAux`; instead it remained CPU-active for over six
minutes while checking that declaration, with roughly 0.8–1.3 GB resident
memory. The run was manually interrupted and ended cleanly with:

```text
Done!
- 1452 entries (2353 possible instances) (including quot).
...
Error at line 92064 (for Char.ofNatAux): ...
User interrupt.
```

This confirms that OCaml 5 removes the fixed native-stack failure, but the
legacy export's missing opacity metadata makes a large proof transparent and
causes pathological checking/unfolding in the following computational
definition. The partial log is
`reports/logs/import_scheduled_rocq_master_ocaml5.log`; it is not a successful
import.

Immediately afterward, upstream pull request 78 was identified at commit
`a6b7fbd64c2aec56014850d235c07bafba67239c` (dated 2026-09-17). It is based
directly on current importer master and explicitly “auto opacif[ies] Prop
lemmas (needed when using old format dumps)” while checking opaque bodies in
parallel under OCaml 5. This directly addresses the observed legacy-opacity
failure mode. The PR requires Rocq API commit
`7e7615999ae9c9a9e9f7a123910c355d713207dd`. The next attempt will use those
exact two upstream commits, retaining the already required UInt32 and Lean
4.33 string-literal patches; no proof will be skipped or admitted.
