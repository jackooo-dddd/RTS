# Revision: `cli/cmd/tui/routes/session/sidebar.tsx` (interactive terminal UI)

**File**: [`cli/cmd/tui/routes/session/sidebar.tsx`](../../../prosabuddy-rocq/packages/opencode/src/cli/cmd/tui/routes/session/sidebar.tsx). **Change size**: Modify, Small. **Priority**: low — the TUI is not used by the
benchmark runner (`opencode run`), so this does not affect proving.

**Current behavior**: shows rocq-lsp status (server state Busy/Idle/Stopped, module name, file progress, execution
ranges, current goal/hypotheses) via the `RocqStatus` type and the `lsp.client.rocq.*` events.

**Change**: follow whatever the Lean LSP client exposes after the port (tools-advices `07-lsp/client-revision.md`):
- [#L13](../../../prosabuddy-rocq/packages/opencode/src/cli/cmd/tui/routes/session/sidebar.tsx#L13), [#L72](../../../prosabuddy-rocq/packages/opencode/src/cli/cmd/tui/routes/session/sidebar.tsx#L72), [#L217-L221](../../../prosabuddy-rocq/packages/opencode/src/cli/cmd/tui/routes/session/sidebar.tsx#L217): same as the status dialog: Lean status, no goal panel.
