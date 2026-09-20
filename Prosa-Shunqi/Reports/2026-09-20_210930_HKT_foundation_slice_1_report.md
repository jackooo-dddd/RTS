# FOUNDATION_SLICE_1 Report

Report started: **2026-09-20 21:09:30 HKT**

Status in this document is cumulative. A declaration is not accepted merely because it compiles.

## 2026-09-20 21:09:30 HKT — Selection and production compile

- Authoritative source: Prosa v0.6 commit `414e66760333eaa4ef78c685bcf53291c527a548`.
- Accepted preparation snapshot identifies `behavior/time.v` as Layer 0, with no direct internal or external dependencies.
- Selected source files: `behavior/time.v` only. The optional allowance of up to two extra Layer-0 files was not used: the smaller candidates have no public declarations, while the next candidates add representation or logical boundaries that would prevent this first slice from remaining a closed two-declaration test.
- Selection evidence: `Validation/planning/v06_pipeline/foundation_slice_1_selection.json`.
- Source inventory: two public definitions, `duration` and `instant`.
- Source file SHA-256: `9fea3f9a3181ca697e8abdb9eee90a656057081f62b00157c3ce9fbe59e53230`.
- Production file created: `Prosa/Behavior/Time.lean`.
- Representation: both source `nat` aliases are Lean `Nat` aliases, following the approved v0.6 mapping policy.
- Production Lean source SHA-256: `aae8e9834a60bdb04abc633fcf10e9441542d7f54f418e596790e800317f9330`.
- `lake env lean Prosa/Behavior/Time.lean`: **PASS**.
- `lake build`: **PASS**.
- Toolchain used: Lean `4.33.1`, Lake `5.0.0`, Mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474`.
- Lake build artifact SHA-256 (diagnostic only; it will not be reused by semantic validation): `0f01cab4f32af7f053b0da9f32703c3f4791e0d85bc6879d06db9b61543d27b3`.
- Proof-valued production declarations: none. Axioms audit is therefore not applicable at this stage; semantic certificates will still receive `Print Assumptions` audits.

Current status:

| Declaration | Lean compile | Semantic certificate | Acceptance |
|---|---:|---:|---:|
| `duration` | PASS | PENDING | NOT YET ACCEPTED |
| `instant` | PASS | PENDING | NOT YET ACCEPTED |

Next gate: fresh isolated Lean compilation, actual-artifact export/import, new Rocq correspondence certificates, and automatic assumption classification.

## 2026-09-20 21:14 HKT — First kernel run and explicit importer boundary

The first end-to-end run reached all eight `Print Assumptions` checks. The fail-closed classifier stopped because it had not yet classified the exact importer message:

```text
Axioms:
Lean.eq relies on definitional UIP.
```

This is not a validation-specific semantic premise and not the Prop/SProp theorem foundation. It is the existing `rocq-lean-import` equality foundation used whenever a certificate concludes imported Lean `SProp` equality. The classifier was tightened to accept only this exact message as `ALLOWED_IMPORTER_FOUNDATION`, while rejecting any additional `Axioms:`, `Assumptions:`, `sorryAx`, `Admitted`, missing output, truncated output, or certificate self-dependency.

No result was accepted during the failed first audit.

## 2026-09-20 21:17:32 HKT — Fresh end-to-end validation passed

The workspace-local command

```bash
./Validation/scripts/validate_foundation_slice_1.sh
```

was rerun from a newly created work directory. It performed the following in order:

1. verified the pinned source commit, clean source worktree, source-file hash, Lean toolchain, and Mathlib revision;
2. compiled `Prosa/Behavior/Time.lean` to a fresh `.olean` outside the Lake build cache;
3. inspected the actual elaborated Lean declarations;
4. exported exactly `Prosa.Behavior.Time.duration` and `Prosa.Behavior.Time.instant` with `lean4export`;
5. copied the pinned official `behavior/time.v` byte-for-byte into a fresh Rocq build root and compiled it with Rocq 9.3;
6. imported the actual Lean export with `rocq-lean-import`;
7. compiled new workspace-local semantic certificates;
8. ran and automatically classified all `Print Assumptions` results;
9. published artifacts only after every preceding step succeeded;
10. regenerated the content-addressed freeze manifest and status JSON.

### Source and target inventory

| Official v0.6 declaration | New production Lean declaration | Migration action | Lean representation |
|---|---|---|---|
| `prosa.behavior.time.duration` | `Prosa.Behavior.Time.duration` | `REUSE_AFTER_REVALIDATION` | reducible alias of `Nat` |
| `prosa.behavior.time.instant` | `Prosa.Behavior.Time.instant` | `REUSE_AFTER_REVALIDATION` | reducible alias of `Nat` |

Whole-file coverage is complete: the official file has exactly these two named public declarations, and both have production counterparts. There are no Lean-only helpers in the production file.

Migration counts:

- `REUSE_AFTER_REVALIDATION`: 2
- `ADAPT_OLD_LEAN`: 0
- `NEW_TRANSLATION`: 0

The old implementation was used only as a representation reference. Both declarations were rebuilt and revalidated against the pinned v0.6 source.

### Compilation and proof cleanliness

| Check | Result |
|---|---|
| Lean 4.33.1 direct file compile | PASS |
| Lake project build | PASS |
| Fresh isolated `.olean` compile | PASS |
| Forbidden `sorry` / custom `axiom` / `unsafe` scan | PASS |
| Production theorem/lemma/instance `#print axioms` set | EMPTY — no proof-valued declarations in this file |
| Official Rocq source compile under Rocq 9.3 | PASS |
| Actual Lean export | PASS |
| Rocq import | PASS |
| Rocq certificate compile | PASS |
| Automatic assumption audit | PASS |

The elaborated declarations inspected from the fresh Lean artifact are:

```text
@[reducible] def Prosa.Behavior.Time.duration : Type := Nat
@[reducible] def Prosa.Behavior.Time.instant : Type := Nat
```

The official Rocq declarations were independently elaborated as:

```text
duration : Set
duration = nat : Set
instant : Set
instant = nat : Set
```

### Semantic relation and certificates

The imported Lean `Nat` is represented in Rocq as a distinct imported inductive. The certificate therefore uses explicit structural conversions:

```text
rocq_nat_to_imported : Rocq nat -> imported Lean Nat
imported_nat_to_rocq : imported Lean Nat -> Rocq nat
```

For each alias, the semantic relation states that the imported value is imported-Lean-equal to the structural image of the Rocq value. Rocq checked:

- relation totality from every Rocq value;
- the Rocq-side roundtrip;
- the imported-Lean-side roundtrip.

This is bidirectional representation correspondence, not source-text comparison and not merely successful Lean compilation.

| Declaration | Own proof | Semantic premises | Prop/SProp foundation | Assumption audit | Final status |
|---|---:|---:|---:|---:|---|
| `duration` | PASS | none | none | PASS with allowed importer equality foundation | `ACCEPTED_V06_TRANSLATION` |
| `instant` | PASS | none | none | PASS with allowed importer equality foundation | `ACCEPTED_V06_TRANSLATION` |

### `Print Assumptions` audit

Eight certificates/bridge lemmas were audited:

- 3 are `Closed under the global context`;
- 5 use exactly `Lean.eq relies on definitional UIP` because their conclusions are imported Lean equality;
- validation-specific semantic premises: none;
- Prop/SProp theorem foundation: none;
- target theorem self-dependency: false;
- unexpected assumptions: none;
- missing or unparsed assumption output: none.

The machine-readable classification is in `Validation/logs/foundation_slice_1/assumption_summary.json`.

### Content-addressed provenance

Final-run hashes:

| Artifact | SHA-256 |
|---|---|
| Official `behavior/time.v` | `9fea3f9a3181ca697e8abdb9eee90a656057081f62b00157c3ce9fbe59e53230` |
| Production `Time.lean` | `aae8e9834a60bdb04abc633fcf10e9441542d7f54f418e596790e800317f9330` |
| Fresh `Time.olean` | `bf431d237f41ff3a54f88adac803f174db6e2f635165a81989f2bfdfe4cbaefb` |
| Lean export `Time.out` | `8b2354769dc908175b0386f4fb1b2113be48db89164e384fe34b5539264e115a` |
| Imported Rocq artifact | `3a10479bbd158ab6625c8d9066dcacd27036c9b99f418a556b317d2d1ebbf3a5` |
| Compiled official Rocq source | `f33c2d9d56538ddbe8be948bdbdc5324e8c36fcaa36714a4d0bd9adb28078fcf` |
| Certificate source | `ed21d40e8159167b155aaa39e9d4b756c468f91c8c224cc1bd1472cdc69bc9b8` |
| Compiled certificate | `5128621639b06b34f55daeb092c46543939b910710f8e1a94bd3de03ce8ded77` |

The freeze manifest records per-declaration source command hashes, elaborated type fingerprints, Lean type hashes, computational body hashes, artifact hashes, and a combined invalidation key. Any change requires rerunning translation validation.

Tool boundary:

- Lean: 4.33.1 (`819816b...`)
- Mathlib: `0df444a360eaa60ab8c11dca51a86af692955474`
- Rocq: 9.3+rc1
- `lean4export`: commit `c9f8373f8a37a65c0ed9bfd20480a3d7481a163e`, patched worktree; exact diff/status hashes and patch are recorded in logs
- `rocq-lean-import`: commit `c9f43ad5c6e8b82d96e50cb5677157bc9cf581e9`, patched worktree; exact diff/status hashes and patch are recorded in logs
- exporter binary and importer plugin/foundation `.vo` hashes are recorded in `runtime_provenance.json`.

The patched tool worktrees are an explicit TCB/provenance boundary; they are not silently described as pristine upstream releases.

## Final result

Production file created:

- `Prosa/Behavior/Time.lean`

Accepted declarations:

- `Prosa.Behavior.Time.duration`
- `Prosa.Behavior.Time.instant`

Blocked declarations: none in the selected file.

Current production coverage truth (only `Prosa-Shunqi/Prosa/` is counted):

| Metric | Count |
|---|---:|
| Accepted v0.6 files | 1 / 357 |
| Accepted v0.6 declarations | 2 / 2439 |
| Translated but not certified | 0 |
| Certified | 2 |
| Proof-clean | 2 |
| Blocked in this slice | 0 |
| Deferred CoqEAL boundary (global inventory) | 239 |

Integrity results:

- historical `Prosa-fei/Prosa/` tracked tree remains unchanged at Git object `7426e874bd049e6f007b2695ef13f7209a0a1f8f`;
- no untracked file was added under `Prosa-fei/Prosa/`;
- pinned v0.6 source is clean and unchanged;
- accepted dependency/mapping planning snapshots are unchanged;
- no stale project `.olean` or validation `.vo` was used by the final run;
- `git diff --check`: PASS.

```text
FOUNDATION_SLICE_1_STATUS = PASS
```

Final integrity check completed: **2026-09-20 21:19:56 HKT**.
