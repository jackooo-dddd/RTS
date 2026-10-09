# Lean 4 Migration Notes for `proof-context.ts`

**Purpose**: Retrieve goals, hypotheses, and diagnostics at the current position from Rocq LSP, and cache and refresh proof snapshots.

**Backend (decided 2026-10-09):** Lean LSP is used for file-level diagnostics and read-only lookups (hover, definitions, references, symbols; no goal operation, DECISIONS D3); tactic execution and goal states the agent acts on come from Pantograph — see [`BACKEND_DECISION.md`](../../BACKEND_DECISION.md).

**1. Goal and Hypothesis Snapshots | Rewrite, Large**

- **Location**: [Line 82: snapshot](../../../prosabuddy-rocq/packages/opencode/src/session/proof-context.ts#L82).

**Source code to adapt** (only the opening lines or key conditions are shown for long blocks):

Rocq goal query entry point, [From line 96](../../../prosabuddy-rocq/packages/opencode/src/session/proof-context.ts#L96):

```ts
    const goals = await LSP.rocqGoals({
      file,
      line: position.line,
      character: position.character,
      mode: "After",
      pp_format: "Str",
```

Reading goal and hypothesis fields, [From line 108](../../../prosabuddy-rocq/packages/opencode/src/session/proof-context.ts#L108):

```ts
    const first = goals?.goals?.goals[0]
    const hyps = first?.hyps.map((h) => `${h.names.join(", ")}: ${h.ty}`) ?? []
    const goal = first?.ty
```

- **Current behavior**: Calls `LSP.rocqGoals` with parameters such as After/Str, and reads `goals[0].ty` and hypothesis names/ty.
- **Recommendation** (**decided, D3**): take the proof snapshot from the `lean_session` goal state of the active region (Pantograph), not from LSP; convert the full local context and goals, preserving instance binders, rather than applying the Rocq goal schema.

**2. Refresh and Completion Events | Rewrite, Medium**

- **Location**: [Line 245: waitIdle](../../../prosabuddy-rocq/packages/opencode/src/session/proof-context.ts#L245).

**Source code to adapt** (only the opening lines or key conditions are shown for long blocks):

Rocq idle-state check, [From line 248](../../../prosabuddy-rocq/packages/opencode/src/session/proof-context.ts#L248):

```ts
    const rocq = statuses.find((s) => s.id === "rocq-lsp")
    if (rocq?.rocq?.state === "Idle") return
```

Rocq status subscription, [From line 254](../../../prosabuddy-rocq/packages/opencode/src/session/proof-context.ts#L254):

```ts
      const unsub = Bus.subscribe(LSP.Event.RocqServerStatus, (event) => {
        if (event.properties.status === "Idle") {
          if (timer) clearTimeout(timer)
```

- **Current behavior**: Waits for rocq-lsp to become Idle; subscribes to RocqExecutionInformation/FileProgress to mark snapshots stale.
- **Recommendation**: Refresh snapshots using the Lean backend's file-processing progress, diagnostics, and document versions; replace all Rocq-specific events and state enums while retaining general diagnostic subscriptions.

Snapshot caching, freshness tracking, diagnostic aggregation, and role-specific rendering structures can be retained.
