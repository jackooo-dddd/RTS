# ScheduledIn actual-artifact import experiment

Experiment start: **2026-09-18 08:13 HKT**  
Snapshot written: **2026-09-18 08:17 HKT**

This report is a focused continuation of `pilot_report.md`. It records only
the current attempt to make the unchanged actual Lean export
`Validation/export/ScheduledIn.out` import completely into Rocq. No semantic
bridge or translated Prosa file is being extended while this import remains
incomplete.

## Exact inputs

- RTS repository commit under validation:
  `845f156a6a75f704361c230870d97566a14b6913`.
- Actual Lean artifact: `export/ScheduledIn.out`, 117,742 lines and 2,598,107
  bytes, exported from the repository's compiled
  `Prosa.Behavior.Schedule.ProcessorState.scheduled_in` declaration.
- Current importer master base:
  `546979bfd55b94288abfb72583a534b0136d282d`.
- Upstream importer PR 78:
  `a6b7fbd64c2aec56014850d235c07bafba67239c`.
- Rocq API commit required by PR 78:
  `7e7615999ae9c9a9e9f7a123910c355d713207dd`.
- Stdlib master used with that Rocq development tree:
  `1593d617cc9496e10be236cda9070d0380c4b252`.
- OCaml: 5.2.1, isolated opam switch `rocq-master-ocaml5`.

## Importer-only changes in this experiment

The working importer is a temporary checkout at
`/private/tmp/rocq-lean-import-current`. None of these changes are in RTS:

1. Upstream `fix-UInt32` commit
   `fc148dfa2e8f27e1a9753e9403d26f0d16440279` was ported onto importer master.
   This replaces the obsolete `UInt32 -> Fin UInt32.size` predeclaration with
   Lean 4.33's actual `UInt32.toBitVec : UInt32 -> BitVec 32` representation.
2. String literals are constructed from the actual imported Lean 4.33 objects
   `List.utf8Encode`, `ByteArray.IsValidUTF8.intro`, `Eq.refl`, and
   `String.ofByteArray`. No axiom or admitted validity proof is used.
3. Upstream PR 78's delayed/parallel opaque checking and legacy automatic
   proof opacity were applied. Its `domainslib` dependency is installed.
4. A local performance refinement determines proof irrelevance from the
   translated declaration type rather than retyping the declaration body.
   This is a temporary importer patch and is not yet an upstream result.

## Confirmed progress before this run

- Current importer dependent-projection support passed legacy line 70,220
  (`Lean.Omega.IntList.dot_sdiv_left`).
- The UInt32 patch passed legacy line 90,537 (`UInt32.toBitVec`).
- The string patch passed line 91,687 (`String.instInhabited`) and all 30
  string literal expressions in this export section.
- A bounded import `0 91990` completed and produced a Rocq `.vo` containing
  1,449 entries. Thus all declarations strictly before line 91,990 have been
  accepted by Rocq's kernel.
- Under OCaml 4, line 91,990 caused native stack exhaustion. Raising the stack
  from 8 MB to 65 MB advanced through line 92,064. Under OCaml 5 the fixed
  native-stack crash disappears, but the legacy export's missing opacity
  metadata causes very expensive checking/unfolding around `Char.ofNatAux`.

## Current live run

Command:

```text
ROCQLI_SRC=/private/tmp/rocq-lean-import-current \
IMPORT_OPAM_SWITCH=rocq-master-ocaml5 \
./scripts/import_lean.sh ImportedScheduled.v \
  > reports/logs/import_scheduled_pr78_typeopacity.log 2>&1
```

At the 08:17 snapshot the process was still CPU-active, with no kernel error,
at:

```text
line 91990: _private.Init.Prelude0.isValidChar_UInt32.match_1_1
line 92040: _private.Init.Prelude0.isValidChar_UInt32
line 92047: Char.ofNatAux._private_1
line 92064: Char.ofNatAux
```

This is **not yet a successful import**. The actual
`Prosa.Behavior.Schedule.ProcessorState.scheduled_in` declaration is not yet
referenceable from a completed Rocq `.vo`, and no actual-artifact semantic
certificate is claimed.

## Current blocker and next action

The current blocker is pathological conversion/checking cost in the Lean 4.33
`Char.ofNatAux` dependency induced by the legacy dump and large Peano-nat
terms. The live PR78 run will be allowed to complete or reach a definite error.
If it remains stuck, the next diagnostic is a sampled native call graph and a
minimal importer optimization that preserves every declaration body and does
not skip or admit any proof. Only after the complete import succeeds will
`ProcessorStateBridge.v` be connected to actual imported Lean objects.

## 08:20 HKT update — upstream check and live-run diagnosis

The type-based-opacity run remained active after 5 minutes 15 seconds. At
that snapshot the worker used approximately 2.23 GiB RSS and 115% CPU, but its
last completed declaration was still `Char.ofNatAux` at legacy line 92,064.
There was no Rocq kernel error and no completed `ImportedScheduled.vo`.

The upstream repository was checked directly with:

```text
git ls-remote --heads https://github.com/rocq-community/rocq-lean-import.git
```

It currently exposes only:

```text
fc148dfa2e8f27e1a9753e9403d26f0d16440279 refs/heads/fix-UInt32
546979bfd55b94288abfb72583a534b0136d282d refs/heads/master
```

Therefore there is no newer upstream branch beyond the already-tested master
and `fix-UInt32` branch that can simply replace the current importer checkout.
The evidence now points specifically to kernel conversion cost for the
computational `Char.ofNatAux` body, not the earlier dependent-projection,
UInt32 representation, string-literal, or native-stack failures.

## 08:22 HKT update — run stopped after measured memory explosion

A two-second native sample was captured in
`/private/tmp/rocq-import-0822.sample`. At 8 minutes elapsed, macOS reported a
22.5 GiB physical footprint for the Rocq worker. The sampled main domain was
inside Rocq `CClosure` construction/conversion, with most samples additionally
spent in OCaml 5 major marking/collection. The import log had not advanced
beyond `Char.ofNatAux`.

The run was therefore stopped with interrupt (exit code 130) to avoid machine
memory exhaustion. This is a definite failed run, not a timeout being counted
as successful progress. Its log is
`reports/logs/import_scheduled_pr78_typeopacity.log`.

The next importer experiment will mark only `Char.ofNatAux` as a delayed
opaque declaration. This does **not** skip or admit its body: PR 78 submits the
body to `Safe_typing.check_opaque`, waits for the resulting certificate at the
end of the import, and installs it with `Global.fill_opaque`. The purpose is to
prevent this computational definition from blocking all subsequent parsing
and to test its body in a worker with an opaque downstream boundary. If that
body does not eventually receive a Rocq kernel certificate, the import will
still be reported as failed.

## 08:24 HKT update — selective delayed opacity unblocks parsing

The temporary importer was changed in exactly one additional place:
`declare_def` forces the legacy declaration named `Char.ofNatAux` through PR
78's delayed opaque-checking path. The importer rebuilt successfully with:

```text
opam exec --switch=rocq-master-ocaml5 -- make -j4
```

The new full import command is:

```text
ROCQLI_SRC=/private/tmp/rocq-lean-import-current \
IMPORT_OPAM_SWITCH=rocq-master-ocaml5 \
./scripts/import_lean.sh ImportedScheduled.v \
  > reports/logs/import_scheduled_pr78_charopaque.log 2>&1
```

After 44 seconds it had passed the former line-92,064 barrier and reached
legacy line 106,578 (`List.exists_of_eraseP`). This is the first run to pass
`Char.ofNatAux`. The change affects opacity/performance only: the declaration
body remains queued for `Safe_typing.check_opaque`, and `finish` must await and
install its kernel certificate before the import command can succeed. Thus
this is confirmed import progress, but **not yet a successful complete
import**.

## 08:28 HKT update — actual target reached; final certificates pending

The same run continued through the translated Prosa dependencies and reached
the final legacy record:

```text
line 111439: Prosa.Behavior.Job.work
line 111491: Prosa.Behavior.Schedule.ProcessorState
...
line 117684: Fintype.decidableExistsFintype
line 117742: Prosa.Behavior.Schedule.ProcessorState.scheduled_in
```

Thus the importer has now parsed and declared the actual target from the
unchanged `ScheduledIn.out` stream. At this snapshot the command was still
running in `finish`; no `Done!`, successful exit code, or `.vo` existed yet.
The remaining condition is crucial: every delayed opaque body must return a
Rocq kernel certificate and be installed before this can be called a genuine
successful import.

## 08:35 HKT update — delayed body check still pathological

The run was allowed to spend approximately 12 minutes in `finish`. A sample
at 11 minutes measured an 8.5 GiB physical footprint; one worker remained in
Rocq `CClosure` conversion while the main domain waited. No delayed
certificate returned, no `Done!` was printed, and no `.vo` was produced. The
run was interrupted and ended with the explicit Rocq message:

```text
File "./ImportedScheduled.v", line 3, characters 0-40:
Error: User interrupt.
```

Therefore selective delayed opacity solves forward import progress but not
the pathological kernel checking cost of the exported `Char.ofNatAux` body.
This run is **FAILED**, despite reaching the target declaration.

The next minimal route is an importer primitive predeclaration for
`Char.ofNatAux`, analogous to the importer's existing predeclarations for
`Nat.add`, `Nat.mul`, `Nat.pow`, `UInt32.size`, and `Nat.isValidChar`. The Rocq
definition will directly implement the Lean 4.33 source construction from a
`Nat` and its `Nat.isValidChar` proof. It must itself compile in Rocq without
axioms. This changes only importer support code; the RTS Lean source and
`ScheduledIn.out` remain unchanged. The report will distinguish this trusted
primitive mapping from checking the exporter-generated pathological body.

## 08:37 HKT milestone — full `ScheduledIn.out` import succeeded

The importer support definition and registration compiled successfully under
Rocq commit `7e7615999ae9c9a9e9f7a123910c355d713207dd`. Its implementation mirrors
Lean 4.33's `Char.ofNatAux`: it constructs a `Char` whose `UInt32` contains
`BitVec.ofFin n`, reuses the supplied `Nat.isValidChar n` proof for the
`Char.valid` field, and proves the `n < 2^32` bound from that validity proof.
The Rocq proof uses no axiom and no admitted fact.

The unchanged actual artifact was then imported with:

```text
ROCQLI_SRC=/private/tmp/rocq-lean-import-current \
IMPORT_OPAM_SWITCH=rocq-master-ocaml5 \
./scripts/import_lean.sh ImportedScheduled.v \
  > reports/logs/import_scheduled_char_predeclared.log 2>&1
```

This command exited with status 0. Its final output was:

```text
line 117742: Prosa.Behavior.Schedule.ProcessorState.scheduled_in

Done!
- 1770 entries (2976 possible instances) (including quot).
1495 parallelized opaques (73.877060s).
- 53 universe expressions
- 11804 names
- 104117 expression nodes
Max universe instance length 5.
0 inductives have non syntactically arity types.
```

Rocq produced `rocq/ImportedScheduled.vo` (8.7 MiB). Therefore the actual
Lean export has now genuinely completed the importer pipeline, including all
of PR 78's delayed kernel checks. The import status is **PASS**.

Important trust-boundary detail: the pathological exporter body of
`Char.ofNatAux` is represented by a new, kernel-checked Rocq primitive
predeclaration, just as other importer primitives are. It is not the raw
exporter body. The actual `scheduled_in` declaration itself is not
predeclared: its exported type and body are translated and checked normally.
The next check is to reference and print that imported target from the
generated `.vo`, then connect the existing bridge to it.

## 08:38 HKT update — imported symbol is directly referenceable

`rocq/ImportedScheduledCheck.v` was compiled against the generated `.vo`.
Rocq accepted all of the following operations:

```text
Check Prosa_Behavior_Schedule_ProcessorState_scheduled_in.
Print Prosa_Behavior_Schedule_ProcessorState_scheduled_in.
Print Assumptions Prosa_Behavior_Schedule_ProcessorState_scheduled_in.
```

The imported constant has type:

```text
forall (Job : Prosa_Behavior_Job_JobType) (State : Type),
  Prosa_Behavior_Schedule_ProcessorState Job State ->
  Job -> State -> Bool
```

Its printed body is the actual expected translation: `Decidable_decide` of an
imported `Exists` over the projected `Core`, whose predicate calls the actual
imported `scheduled_on` and compares it with `Bool_true`. The independent
check log is `reports/logs/imported_scheduled_check.log`.

The target's reported assumptions are the importer's established Lean model
boundary: definitional UIP for imported equality/HEq/True, `propext`, the
registered `PrimInt63` primitives, `Quot_sound`, and `Classical_choice`. No
new validation-specific axiom appears.

## 08:42 HKT update — cross-certificate toolchain alignment

`ProcessorStateBridge.v` has been connected in source to the real imported
`ProcessorState`, `Core`, `scheduled_on`, and `scheduled_in` constants. It now
defines an explicit Rocq-bool/imported-Lean-Bool relation in `SProp` and a
candidate compositional theorem based only on core-surjectivity and
`scheduled_on` preservation. This candidate is **not yet claimed as passed**.

Compilation exposed a binary toolchain boundary: the exact Prosa 0.6 Rocq
package is installed under Rocq 9.0.1, whereas `ImportedScheduled.vo` was
created by the Rocq 9.4-alpha importer API branch. Rocq `.vo` files cannot be
mixed across those kernels. A Rocq 9.3 RC1 switch is therefore being prepared
to host both sides. Its packages are pinned with the opam version `dev`, which
requires overriding the package solver's otherwise-applicable `<9.4` MathComp
constraint. A first full-algebra install also exposed an unrelated packaging
failure: micromega 1.1.1 uses Dune's removed `(using coq 0.8)` extension under
Dune 3.24. The next attempt is restricted to the MathComp core needed by the
schedule slice and a direct build of the exact Prosa 0.6 sources.

## 09:15 HKT update — same-kernel Rocq 9.3 import also succeeded

The cross-certificate toolchain was aligned successfully:

- Rocq: 9.3 RC1 commit `67e678adcd0cb911fec4eca313d9843492881956`;
- MathComp: 2.6.0, built under that Rocq;
- Dune: 3.23.1 (new enough for Rocq 9.3 and still compatible with the
  MathComp/HB package build language);
- exact Prosa source: cached v0.6 release source previously installed from the
  package checksum recorded in the main report.

To compile just the target source closure under Rocq 9.3, three compatibility
changes were made only in the temporary cached Prosa source:

1. `util/tactics.v` preserves the current ssreflect `done` tactic under a
   helper name before defining Prosa's wrapper;
2. `util/seqset.v` rewrites the removed legacy binder syntax
   `set_of of phant T` as `set_of (_ : phant T)`;
3. `behavior/job.v` replaces the overly broad `Require Export
   prosa.util.all` with the MathComp modules actually needed by this 24-line
   file. This dependency-pruning patch avoids compiling unrelated Prosa
   utility proofs that changed between MathComp 2.4 and 2.6. The declarations
   `JobType`, `work`, `JobCost`, `JobArrival`, and `JobDeadline` are unchanged.

With that pruning, Rocq 9.3 compiled the original v0.6 `behavior/time.v`,
`behavior/job.v`, `behavior/arrival_sequence.v`, and `behavior/schedule.v`.
In particular, the original `scheduled_in` declaration body was not edited.

A clean importer worktree at `/private/tmp/rocq-lean-import-93` was based on
current importer master `546979bfd55b94288abfb72583a534b0136d282d`, with:

- upstream `fix-UInt32` applied;
- the earlier dependent-projection implementation;
- the Lean 4.33 `String.ofByteArray` adapter;
- the kernel-checked `Char.ofNatAux` primitive predeclaration;
- mechanical `Summary.Ref` to `Summary.ref` source compatibility for Rocq
  9.3.

It imported the unchanged `ScheduledIn.out` with a 65,520 KiB native stack:

```text
ulimit -s 65520
ROCQLI_SRC=/private/tmp/rocq-lean-import-93 \
IMPORT_OPAM_SWITCH=rocq93rc1 \
./scripts/import_lean.sh ImportedScheduled93.v \
  > reports/logs/import_scheduled_rocq93_predeclared.log 2>&1
```

The command exited 0 and printed:

```text
line 117742: Prosa.Behavior.Schedule.ProcessorState.scheduled_in

Done!
- 1770 entries (2976 possible instances) (including quot).
- 53 universe expressions
- 11804 names
- 104117 expression nodes
Max universe instance length 5.
0 inductives have non syntactically arity types.
```

`rocq/ImportedScheduled93.vo` is therefore a complete actual-artifact import
checked by the same Rocq 9.3 kernel that now has the original Prosa 0.6
schedule source available. The next action is compiling the connected
`ProcessorStateBridge.v`; no `completed_by` work begins before that result.

## 09:30 HKT milestone — first actual-artifact certificate accepted

`rocq/ProcessorStateBridge.v` now directly imports `ImportedScheduled93` and
mentions all of the real imported Lean objects:

- `Prosa_Behavior_Schedule_ProcessorState`;
- `Prosa_Behavior_Schedule_ProcessorState_Core`;
- `Prosa_Behavior_Schedule_ProcessorState_scheduled_on`;
- `Prosa_Behavior_Schedule_ProcessorState_scheduled_in`.

The obsolete abstract Lean-side `CoreL : finType`, `scheduled_onL`, and
handwritten `scheduled_inL_model` section was removed. The replacement theorem
is:

```text
scheduled_in_actual_artifact_bridge
```

It relates the original v0.6 `prosa.behavior.schedule.scheduled_in` directly to
the actual imported Lean constant with an explicit `ImportedBoolRel` between
MathComp `bool` and imported Lean `Bool`.

The proof is compositional over exactly the observable interface needed here:

1. `toL` and `toR` relate original and Lean core values;
2. `core_surjective : forall cL, toL (toR cL) = cL` ensures every Lean core
   has an original representative;
3. `scheduled_on_rel` preserves the boolean observation for related cores;
4. `mathcomp_exists_as_has_enum` connects MathComp's finite quantifier to its
   concrete enumeration;
5. `imported_exists_forward_seq` recursively traverses that enumeration in
   `SProp`, avoiding any forbidden elimination of a `Prop` witness into
   imported Lean `SProp`;
6. `imported_decide_bridge` proves the correspondence of imported
   `Decidable_decide` with the original boolean result.

Compilation command:

```text
opam exec --switch=rocq93rc1 -- rocq c \
  -R /Users/shunqiwang/.opam/prosa-0.6/.opam-switch/sources/rocq-prosa.0.6 prosa \
  -Q /private/tmp/rocq-lean-import-93/src LeanImport \
  -I /private/tmp/rocq-lean-import-93/src \
  ProcessorStateBridge.v
```

The command exited 0 and generated `ProcessorStateBridge.vo`. No `Axiom`,
`Admitted`, or `sorry` was added.

`rocq/ScheduledInActualAudit.v` then ran:

```text
Print Assumptions scheduled_in_actual_artifact_bridge.
```

The output is saved verbatim in
`reports/logs/scheduled_in_actual_assumptions.log`. It lists only the importer's
established Lean model assumptions: definitional UIP for imported equality,
HEq, True, and the local STrue representation; `propext`; registered
`PrimInt63` primitives; `Quot_sound`; and `Classical_choice`. There is no
validation-specific global axiom.

The semantic status is currently **CONDITIONAL**, not `CERTIFIED`, because
`core_surjective` and `scheduled_on_rel` remain explicit theorem premises and
have not been instantiated for a concrete pair of processor-state
representations. The theorem itself and the actual imported declaration are
Rocq-kernel checked. This establishes outcome B from the pilot question: the
existing translation supports a direct actual-artifact correspondence theorem
once an explicit observable processor-state relation is supplied.

## 09:33 HKT milestone — scheduled_in polarity mutation rejected

A validation-only negative fixture was added at
`rocq/ScheduledInPolarityMutation.v`. It leaves both the production Lean source
and `export/ScheduledIn.out` unchanged. The fixture defines
`scheduled_in_polarity_mutation` by applying an imported-`Bool` negation to the
result of the **actual imported**
`Prosa_Behavior_Schedule_ProcessorState_scheduled_in` declaration.

The fixture then places the existing actual-artifact proof term in a
`Fail Definition` whose required conclusion mentions the polarity-mutated
result. This is a Rocq-checked negative assertion: the fixture compiles only
when Rocq rejects that invalid certificate, and would itself fail if the proof
term were accepted for the mutation.

Command:

```text
opam exec --switch=rocq93rc1 -- rocq c \
  -R /Users/shunqiwang/.opam/prosa-0.6/.opam-switch/sources/rocq-prosa.0.6 prosa \
  -Q /private/tmp/rocq-lean-import-93/src LeanImport \
  -I /private/tmp/rocq-lean-import-93/src \
  ScheduledInPolarityMutation.v
```

The command exited 0. Its complete output is saved in
`reports/logs/scheduled_in_mutation.log`. Therefore:

```text
Mutation Detection:
scheduled_in polarity mutation: PASS (invalid certificate rejected by Rocq)
```

The first logging wrapper used `status` as a shell variable, which is readonly
in zsh; that wrapper returned nonzero after Rocq had compiled the fixture. The
command was immediately rerun with `rc`, produced `ROCQ_EXIT=0`, and the log now
contains the clean rerun. This shell-wrapper issue did not affect any Rocq
source or certificate.

Current target status remains **CONDITIONAL** rather than `CERTIFIED`: actual
Lean import, own proof, assumption audit, and mutation rejection now pass, but
the explicit `core_surjective` and `scheduled_on_rel` representation premises
are not yet closed for a concrete processor-state representation.

## 09:36 HKT milestone — one-command certificate verification passes

Added executable `scripts/verify_scheduled_in_actual.sh`. With the already
completed import, it performs the following checks in one run:

1. rejects `Admitted`, `Axiom`, or `sorry` in the actual bridge, audit, and
   mutation sources;
2. recompiles `Relations.v` and `FiniteBridge.v` under Rocq 9.3;
3. recompiles `ProcessorStateBridge.v` against the imported artifact and the
   compatible Prosa v0.6 source closure;
4. prints the type and full body of the actual imported `scheduled_in`;
5. runs `Print Assumptions scheduled_in_actual_artifact_bridge`;
6. recompiles the polarity-mutation rejection fixture.

Exact invocation used:

```text
ROCQLI_SRC=/private/tmp/rocq-lean-import-93 \
IMPORT_OPAM_SWITCH=rocq93rc1 \
PROSA_ROCQ_SRC=/Users/shunqiwang/.opam/prosa-0.6/.opam-switch/sources/rocq-prosa.0.6 \
./scripts/verify_scheduled_in_actual.sh
```

It exited 0 and ended with:

```text
scheduled_in actual-artifact certificate: CONDITIONAL PASS
scheduled_in polarity mutation rejection: PASS
```

The refreshed assumption log now also contains the imported declaration body.
It confirms that the result is exactly `Decidable_decide` over an imported
`Exists` whose predicate is imported `scheduled_on ... = Bool_true`, using the
imported `Core_fintype` instance. Thus the theorem is connected to the actual
Lean definition, not a separately handwritten Rocq model.

`README.md` was updated to remove the obsolete “pipeline blocked” statement
and to distinguish this conditional actual-artifact result from the still
unconnected `completed_by` scaffolding. Setting `REIMPORT=1` on the new script
also reruns the full `ScheduledIn.out` import before certificate verification.

Current summary:

| Target | Actual Lean imported? | Own proof | Dependency closure | Assumptions audited | Mutation rejected | Status |
| --- | --- | --- | --- | --- | --- | --- |
| `scheduled_in` | yes | pass | conditional on explicit core/scheduled-on relation | yes; no validation-specific global axiom | yes | **CONDITIONAL** |
| `completed_by` | not attempted in this focused continuation | N/A | N/A | N/A | N/A | **BLOCKED / out of current scope** |

No file under `Prosa-fei/Prosa/` or `Prosa-fei/Prosa/Classic/` was modified.
The next minimal semantic step, if requested later, is to instantiate
`core_surjective` and `scheduled_on_rel` for a concrete original/imported
processor-state pair. No further bridge is being added in this experiment.

## 10:23 HKT milestone — temporary compatibility changes preserved

The successful environment no longer depends only on mutable `/private/tmp`
and opam-cache edits. Exact replay patches were saved under
`Validation/patches/`:

- `rocq-lean-import-rocq93.patch` (438 lines, 16,501 bytes, SHA-256
  `0b3f5ad7903d43ee211f77d92a814ab799d0392bd6848d6eec5906a16b5de3f4`),
  based on importer commit
  `546979bfd55b94288abfb72583a534b0136d282d`;
- `prosa-v0.6-rocq93-compat.patch` (51 lines, 1,804 bytes, SHA-256
  `13445be1852086af6a51f10dad7dab2a75e3b7bd45e9e1edd7b119fe898a45d9`),
  based on the exact checksum-identified Prosa v0.6 archive.

Both were independently replay-tested from clean baselines with
`git apply --check` followed by `git apply`. The reconstructed importer files
had exactly the same SHA-256 hashes as the successful importer worktree:

```text
0bcd27a0c45bb454ab6a21c518db2f23bbca588bc7a327ae16561b359ad19345  src/Lean.v
ba2b6c3d85c135afad611ea4cc61b37b8541f0eb0502c728eac59ebed7e523b6  src/lean.ml
```

The four reconstructed Prosa compatibility files likewise matched the source
cache used for the successful run byte-for-byte. `patches/README.md` records
the baseline commits/checksum, application commands, trust-boundary purpose,
and the fact that `behavior/schedule.v` and its `scheduled_in` definition are
unchanged.

This is preservation/reproducibility work only. It introduces no new semantic
premise, proof, or Prosa target.

## 10:24 HKT artifact fingerprint snapshot

The exact inputs and checked products present after the successful one-command
rerun are:

```text
5a74e399159e3f2b8100d908ddbab45e3a65928bc43a6f7960ed95d1a67da37e  export/ScheduledIn.out (2,598,107 bytes)
0e29f3ffb24bd6ad32bf56f6f8a96a7809a292829e0f262e7126115d6d04f8d4  rocq/ImportedScheduled93.vo (4,643,996 bytes)
3d33db023818ccfadc77522370e64b65cd8070feebd721dfb3438afccbfc0624  rocq/ProcessorStateBridge.v
ca5feef9f3c988b12fabace3729e5acb27870cca0f774f8234e22b2581113040  rocq/ProcessorStateBridge.vo (125,519 bytes)
da23a75b16ae7e75045db9310f91c3f4a01a8b456ba5a6a9fed3778d9756fcb1  rocq/ScheduledInPolarityMutation.v
d8ca0bc037132d680079e0a1bbdb1348f539ca34dbbde5c64306c1c097adf8f3  rocq/ScheduledInPolarityMutation.vo (109,684 bytes)
```

These fingerprints distinguish the actual imported Lean artifact and
kernel-produced certificate objects from source-only scaffolding.
