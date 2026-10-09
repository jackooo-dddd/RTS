# Revision: `cli/cmd/tui/util/lsp.ts` (interactive terminal UI)

**File**: [`cli/cmd/tui/util/lsp.ts`](../../../prosabuddy-rocq/packages/opencode/src/cli/cmd/tui/util/lsp.ts). **Change size**: Modify, Small. **Priority**: low — the TUI is not used by the
benchmark runner (`opencode run`), so this does not affect proving.

**Current behavior**: shows rocq-lsp status (server state Busy/Idle/Stopped, module name, file progress, execution
ranges, current goal/hypotheses) via the `RocqStatus` type and the `lsp.client.rocq.*` events.

**Change**: follow whatever the Lean LSP client exposes after the port (tools-advices `07-lsp/client-revision.md`):
- [#L15-L36](../../../prosabuddy-rocq/packages/opencode/src/cli/cmd/tui/util/lsp.ts#L15): replace `RocqStatus` by a `LeanStatus` (server state, file progress from Lean's `$/lean/fileProgress`); drop `current.goal/hyps` (goals belong to `lean_session`, D1/D3).
- [#L38-L58](../../../prosabuddy-rocq/packages/opencode/src/cli/cmd/tui/util/lsp.ts#L38) `pickLsp`, [#L76-L106](../../../prosabuddy-rocq/packages/opencode/src/cli/cmd/tui/util/lsp.ts#L76) `rocqProgress/rocqExecution/rocqEnv/rocqGoal`: rename to Lean equivalents; delete `rocqGoal` and `rocqExecution` if the Lean client does not provide them.
