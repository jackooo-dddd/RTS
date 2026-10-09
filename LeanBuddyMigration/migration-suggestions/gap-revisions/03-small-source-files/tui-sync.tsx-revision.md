# Revision: `cli/cmd/tui/context/sync.tsx` (interactive terminal UI)

**File**: [`cli/cmd/tui/context/sync.tsx`](../../../prosabuddy-rocq/packages/opencode/src/cli/cmd/tui/context/sync.tsx). **Change size**: Modify, Small. **Priority**: low — the TUI is not used by the
benchmark runner (`opencode run`), so this does not affect proving.

**Current behavior**: shows rocq-lsp status (server state Busy/Idle/Stopped, module name, file progress, execution
ranges, current goal/hypotheses) via the `RocqStatus` type and the `lsp.client.rocq.*` events.

**Change**: follow whatever the Lean LSP client exposes after the port (tools-advices `07-lsp/client-revision.md`):
- [#L115-L117](../../../prosabuddy-rocq/packages/opencode/src/cli/cmd/tui/context/sync.tsx#L115): listen to the Lean client's events (e.g. `lsp.client.lean.file-progress`) instead of `lsp.client.rocq.server-status / file-progress / execution-information`.
