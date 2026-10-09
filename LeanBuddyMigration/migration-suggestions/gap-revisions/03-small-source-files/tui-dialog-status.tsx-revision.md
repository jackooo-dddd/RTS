# Revision: `cli/cmd/tui/component/dialog-status.tsx` (interactive terminal UI)

**File**: [`cli/cmd/tui/component/dialog-status.tsx`](../../../prosabuddy-rocq/packages/opencode/src/cli/cmd/tui/component/dialog-status.tsx). **Change size**: Modify, Small. **Priority**: low — the TUI is not used by the
benchmark runner (`opencode run`), so this does not affect proving.

**Current behavior**: shows rocq-lsp status (server state Busy/Idle/Stopped, module name, file progress, execution
ranges, current goal/hypotheses) via the `RocqStatus` type and the `lsp.client.rocq.*` events.

**Change**: follow whatever the Lean LSP client exposes after the port (tools-advices `07-lsp/client-revision.md`):
- [#L7](../../../prosabuddy-rocq/packages/opencode/src/cli/cmd/tui/component/dialog-status.tsx#L7), [#L15](../../../prosabuddy-rocq/packages/opencode/src/cli/cmd/tui/component/dialog-status.tsx#L15), [#L124-L190](../../../prosabuddy-rocq/packages/opencode/src/cli/cmd/tui/component/dialog-status.tsx#L124): render the Lean status fields from `util/lsp.ts`; remove the goal panel.
