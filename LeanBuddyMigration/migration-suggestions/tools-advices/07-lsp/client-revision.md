# Lean 4 Migration Notes for `client.ts`

**Purpose**: Implement LSP client communication, file synchronization, and diagnostic handling, and maintain Rocq-specific events and the current proof state.

**Backend (decided 2026-10-09):** Lean LSP is used for file-level diagnostics and read-only lookups (hover, definitions, references, symbols; no goal operation, DECISIONS D3); tactic execution and goal states the agent acts on come from Pantograph — see [`BACKEND_DECISION.md`](../../BACKEND_DECISION.md).

**1. Rocq Notifications and State | Rewrite, Large**

- **Location**: [Line 219](../../../prosabuddy-rocq/packages/opencode/src/lsp/client.ts#L219).

**Source code to adapt** (only the opening lines or key conditions are shown for long blocks):

Coq server notification handling, [From line 219](../../../prosabuddy-rocq/packages/opencode/src/lsp/client.ts#L219):

```ts
    connection.onNotification("$/coq/serverStatus", (params) => {
      if (input.serverID !== "rocq-lsp") return
      const status = z
        .object({
          status: z.union([z.literal("Busy"), z.literal("Idle"), z.literal("Stopped")]),
          modname: z.string().optional(),
```

- **Current behavior**: Handles Coq serverStatus, fileProgress, and executionInformation, maintaining rocq state and events.
- **Recommendation**: Use the current Lean server's actual notifications/requests to represent file-processing progress and update event data; do not directly treat Rocq Idle or execution information as Lean validation.

**2. Refreshing the Current Proof State | Rewrite, Large**

- **Location**: [Line 154: refreshCurrent](../../../prosabuddy-rocq/packages/opencode/src/lsp/client.ts#L154).

**Source code to adapt** (only the opening lines or key conditions are shown for long blocks):

Current-goal request, [From line 166](../../../prosabuddy-rocq/packages/opencode/src/lsp/client.ts#L166):

```ts
        .sendRequest("proof/goals", {
          textDocument: {
            uri: info.uri,
          },
          position: {
```

Rocq goal parsing, [From line 190](../../../prosabuddy-rocq/packages/opencode/src/lsp/client.ts#L190):

```ts
      const parsed = RocqGoalSnapshot.safeParse(result)
      if (!parsed.success) {
        rocq.current = {
```

- **Current behavior**: Sends proof/goals requests, parses current goals/hypotheses with RocqGoalSnapshot, and maintains a sequence number.
- **Recommendation**: Use Lean goal queries and context parsing, bound to document versions and query positions; retain rejection of stale request results.

**3. Exposed State Object | Modify, Medium**

- **Location**: [Line 434](../../../prosabuddy-rocq/packages/opencode/src/lsp/client.ts#L434).

**Source code to adapt** (only the opening lines or key conditions are shown for long blocks):

Rocq state exposed to callers, [From line 434](../../../prosabuddy-rocq/packages/opencode/src/lsp/client.ts#L434):

```ts
      get rocq() {
        return rocq
      },
```

- **Current behavior**: Exposes rocq-specific state alongside general communication in the same returned client object.
- **Recommendation**: Replace the state interface and Rocq type/event definitions and update callers; the general LSP client need not be rewritten.

JSON-RPC connections, initialization, standard diagnostics, didOpen/didChange, and shutdown can be reused.
