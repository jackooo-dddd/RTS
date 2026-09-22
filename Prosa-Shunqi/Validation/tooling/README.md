# Reproducible validation tooling

The semantic validator uses pinned, workspace-local builds of `lean4export`
and `rocq-lean-import`. Their checked-in patches reproduce the audited base
tool state and the generic validation features used by the current pipeline.
The exporter includes an opt-in
`LEAN4EXPORT_PRESERVE_REDUCIBLE_THEOREM_TYPES=1` mode: after a selected
subexpression projection has passed `Meta.isDefEq`, it preserves that projected
expression instead of globally unfolding unrelated reducible terms. This is
needed for theorem types containing Boolean recursors and does not bypass the
kernel normalization guard.

The Slice 1 importer worktree was based on local commit `c9f43ad…`, which is
not fetchable from the official GitHub remote.  Its checked-in reproduction
therefore starts from reachable upstream commit `546979b…`; the importer patch
contains both the complete `546979b… -> c9f43ad…` UInt32 change and the later
Rocq 9.3 compatibility edits. It additionally fixes recursor generation for
an inductive such as `Option` whose sort is squashable only at some universe
instances: the importer now decides Type-versus-SProp elimination from the
current instantiated result sort, rather than from the global inductive
classification. This is needed for the actual `List.getD` computation exported
by `util/nondecreasing.v`; it adds no axiom or semantic assumption.

Run:

```bash
./setup_validation_tooling.sh
```

The resulting worktrees are created under
`Validation/.work/tooling/`.  The setup fails closed on base-commit, patch,
worktree-diff, toolchain, or output-artifact mismatch.  `Export.lean.orig` is
recreated only to reproduce the recorded Slice 1 worktree status; it is not a
build input.

## Incremental validation protocol

New file validators should use the shared content-addressed protocol rather
than copying a complete shell pipeline:

```bash
Validation/scripts/run_incremental_validation.sh prepare \
  --name NAME --config DESCRIPTOR.json --hooks HOOKS.sh
Validation/scripts/run_incremental_validation.sh check \
  --name NAME --config DESCRIPTOR.json --hooks HOOKS.sh
Validation/scripts/run_incremental_validation.sh finalize \
  --name NAME --config DESCRIPTOR.json --hooks HOOKS.sh
```

`incremental_validation_state.py` binds the prepared snapshot to declared
source/production/dependency files, exact tool binaries, repository commits,
versions, options, and module-loading configuration. It hashes every declared
prepared output before reuse. Missing, mismatched, or damaged artifacts fail
closed. The hooks contain only file-specific build, extraction, export/import,
certificate, audit, and publication actions.

The evidence schema records `lean_build`, `source_acquisition`, `export`,
`rocq_import`, `certificate_compile`, `assumption_audit`, and `publication`,
including execution counts, `FRESH`/`VERIFIED_CACHE` mode, elapsed time, input
fingerprint, and output hashes. Certificate/audit files belong to the check
fingerprint, not the prepared snapshot, so a certificate-only edit reuses a
verified prepare cache but recompiles and re-audits the affected certificate
DAG. `CLEAN_FULL=1` remains available for independent reproduction.

`export_actual_artifact.sh` is the config-driven exporter entry point.
[`export_patterns.json`](export_patterns.json) records the approved uses of
statement-only export, computation-equation bodies, definition-body
projection, guarded normalization, and universe-sensitive datatype
interfaces. A normalized export without a declared kernel guard is rejected.

`generate_artifact_bool_list_adapter.py` instantiates the audited template in
`Validation/templates/ArtifactBoolListAdapter.v.tpl`. Generated adapters prove
Bool truth, `eqType`/`DecidableEq`, ordered `seq`/`List` roundtrips, and
membership against the exact imported datatype; they are ordinary Rocq source
and must pass kernel compilation and the normal assumption classifier.
The generator now declares its provided operations and rejects an unsupported
`--require-operation` with `missing operation bridge: X`. The discovery routes
for already proved length/getD/append/filter/head/last/membership/dedup/index
and Nat order/sub/max adapters are catalogued in
[`artifact_adapter_operations.json`](artifact_adapter_operations.json); a
catalog entry is not acceptance evidence until instantiated against, compiled
with, and audited for the actual imported artifact.

For files with many declarations,
`audit_operation_inventory.py` checks a pre-freeze operation inventory against
content-addressed certificate `.vo` files and actual-artifact evidence. It
fails closed on absent, stale, or uncertified operations and emits the exact
`missing operation bridge: X` obligations before a costly snapshot is frozen.

`incremental_validation_state.py materialize` copies selected groups from a
sealed prepare cache into an isolated consumer root. It verifies the complete
producer descriptor and every source/destination hash. Its evidence explicitly
does not infer semantic acceptance; the consumer must bind that evidence in
its own descriptor. This supports reuse of accepted dependency `.olean` and
imported `.vo` bytes without silently resolving same-named files elsewhere.

Imported `.vo` files are foundation-sensitive. If `LeanImport.Lean` changes,
stable `.out` bytes are re-imported with their checked wrapper source and only
the resulting sealed `.vo` is reused. The workflow regression now exercises
this pattern instead of copying the legacy `ImportedSubadditivity.vo`.

The 2026-09-22 regression sample covers accepted Sum (25 declarations), Poet
(1), and Bigcat (13). Its cold prepare measured 100.29 s for the isolated Lean
closure; an identical rerun verified all four prepare stages from cache in
0.019 s. The final adapter check/finalize took 4.24 s. All 18 generated adapter
checks had no semantic premise or unexpected assumption; only Bool-truth and
membership used the existing `PropSPropFoundation.interpret_strict` boundary.
The existing 39 semantic results were unchanged. Evidence is under
`Validation/logs/incremental/workflow_regression/`.

The 21:32 extension regression added the operation-inventory and dependency
materialization checks. Deleting the interval-sum bridge and corrupting an
imported `.vo` were both rejected. A current-foundation fresh regression of
Sum/Poet/Bigcat passed in 106.71 s (29.41 s Lean build, 75.56 s Rocq re-import,
1.62 s certificate compile); an identical rerun used four verified prepare
cache hits and completed its checks/publication in 1.86 s. Semantic results and
the acceptance gate remained unchanged.
