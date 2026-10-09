# Lean 4 Migration Notes for `index.ts`

**Purpose**: Provide unified LSP interfaces and wrap Rocq goal queries, Petanque interaction, and proof-state data.

**Backend (decided 2026-10-09):** Lean LSP is used for file-level diagnostics and read-only lookups (hover, definitions, references, symbols; no goal operation, DECISIONS D3); tactic execution and goal states the agent acts on come from Pantograph — see [`BACKEND_DECISION.md`](../../BACKEND_DECISION.md).

**1. Goal Requests and Data Structures | Rewrite, Large**

- **Location**: [Line 67: RocqHyp](../../../prosabuddy-rocq/packages/opencode/src/lsp/index.ts#L67).

**Source code to adapt** (only the opening lines or key conditions are shown for long blocks):

Rocq hypothesis data structure, [From line 67](../../../prosabuddy-rocq/packages/opencode/src/lsp/index.ts#L67):

```ts
  const RocqHyp = z.object({
    names: z.array(z.string()),
    ty: z.string(),
  })
```

Rocq goal query protocol, [From line 661](../../../prosabuddy-rocq/packages/opencode/src/lsp/index.ts#L661):

```ts
      client.connection.sendRequest("proof/goals", {
        textDocument: {
          uri: pathToFileURL(input.file).href,
        },
```

- **Current behavior**: RocqHyp/RocqGoal/RocqGoalAnswer represent hypotheses, stack, shelf, and related data; `rocqGoals` sends proof/goals.
- **Recommendation** (**decided, D3**): no LSP goal query in the Lean version; drop `rocqGoals` and its schemas. Goals and local context (with instance binders) come from `lean_session` (Pantograph).

**2. Petanque and Document/Artifact Interfaces | Rewrite or Remove, Large**

- **Location**: [Line 702: rocqPetanqueStart](../../../prosabuddy-rocq/packages/opencode/src/lsp/index.ts#L702).

**Source code to adapt** (only the opening lines or key conditions are shown for long blocks):

Petanque request dispatch, [From line 710](../../../prosabuddy-rocq/packages/opencode/src/lsp/index.ts#L710):

```ts
      const result = input.theorem
        ? await client.connection.sendRequest("petanque/start", {
            uri,
            thm: input.theorem,
          })
```

Coq compilation-artifact request, [From line 694](../../../prosabuddy-rocq/packages/opencode/src/lsp/index.ts#L694):

```ts
      client.connection.sendRequest("coq/saveVo", {
        textDocument: {
          uri: pathToFileURL(input.file).href,
        },
```

- **Current behavior**: Wraps dedicated requests such as Petanque start/run/goals, coq/getDocument, and coq/saveVo.
- **Recommendation**: Move interactive execution/state restoration to the selected Lean backend and connect document queries to Lean capabilities. Remove the saveVo-specific interface and delegate build artifacts to Lean/Lake; changing the extension to `.olean` alone is insufficient.

**3. Server Selection and Event Exports | Modify, Medium**

- **Location**: [Line 639: isRocq](../../../prosabuddy-rocq/packages/opencode/src/lsp/index.ts#L639).

**Source code to adapt** (only the opening lines or key conditions are shown for long blocks):

Rocq server selection, [From line 639](../../../prosabuddy-rocq/packages/opencode/src/lsp/index.ts#L639):

```ts
  function isRocq(client: LSPClient.Info) {
    return client.serverID === "rocq-lsp"
  }
```

- **Current behavior**: Selects the rocq-lsp server and exports Rocq state and events.
- **Recommendation**: Use Lean services and events and update subscribers such as proof-context/session-proof together; retain general LSP dispatch.

Standard LSP interfaces for file synchronization, diagnostics, definitions, and references can be retained.
