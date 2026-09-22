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
Rocq 9.3 compatibility edits.  This yields the same tracked source state as the
tool used in Slice 1.

Run:

```bash
./setup_validation_tooling.sh
```

The resulting worktrees are created under
`Validation/.work/tooling/`.  The setup fails closed on base-commit, patch,
worktree-diff, toolchain, or output-artifact mismatch.  `Export.lean.orig` is
recreated only to reproduce the recorded Slice 1 worktree status; it is not a
build input.
