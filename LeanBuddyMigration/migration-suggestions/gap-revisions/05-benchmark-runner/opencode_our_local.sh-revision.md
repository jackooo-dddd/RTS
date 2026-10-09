# Revision: `scripts/scripts_junyi/opencode_our_local.sh` (starts the OpenCode app)

**File**: [`opencode_our_local.sh`](../../../prosabuddy-rocq/scripts/scripts_junyi/opencode_our_local.sh) (28 lines). **Change size**: Modify, Small.

| Line | Current | Change |
|---|---|---|
| [#L6](../../../prosabuddy-rocq/scripts/scripts_junyi/opencode_our_local.sh#L6) | `OPENCODE_DIR="${OPENCODE_DIR:-/home/junyi/prosabuddy/packages/opencode}"` | default relative to the repository (`$PROJECT_ROOT/packages/opencode`), no home path. |
| [#L7](../../../prosabuddy-rocq/scripts/scripts_junyi/opencode_our_local.sh#L7) | `OPENCODE_CONFIG_DIR_DEFAULT="/home/junyi/prosabuddy/.opencode"` | `$PROJECT_ROOT/.opencode`. |
| rest | bun discovery, `bun run --cwd … ./src/index.ts` | unchanged; additionally export the Lean toolchain `PATH` (elan) so `lean_check`/`lake` resolve the pinned v4.33.1. |
