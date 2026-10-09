# Lean 4 Migration Notes for `session-proof.ts`

**Purpose**: Manage session bindings to proof files and positions, preserve original-source baselines, and track stale state.

**1. Original-Source Baseline | Modify, Small**

- **Location**: [Line 99](../../../prosabuddy-rocq/packages/opencode/src/session/session-proof.ts#L99).

**Source code to adapt** (only the opening lines or key conditions are shown for long blocks):

Coq file baseline capture, [From line 99](../../../prosabuddy-rocq/packages/opencode/src/session/session-proof.ts#L99):

```ts
      if (!file.endsWith(".v")) return undefined
      try {
        return readFileSync(file, "utf-8")
      } catch {
```

- **Current behavior**: The set flow captures canonicalSource only for `.v`, for later proof audits.
- **Recommendation**: Switch to `.lean` so Lean tasks also preserve an original baseline that candidate changes cannot replace.

**2. Rocq State Invalidation Notifications | Modify, Medium**

- **Location**: [Line 248](../../../prosabuddy-rocq/packages/opencode/src/session/session-proof.ts#L248).

**Source code to adapt** (only the opening lines or key conditions are shown for long blocks):

Rocq execution-information subscription, [From line 248](../../../prosabuddy-rocq/packages/opencode/src/session/session-proof.ts#L248):

```ts
    Bus.subscribe(LSP.Event.RocqExecutionInformation, (event) => {
      for (const [sid, b] of cache) {
        if (b.file.endsWith(event.properties.uri) || event.properties.uri.endsWith(b.file.split("/").pop()!))
          markStale(sid)
      }
```

- **Current behavior**: Listens to Rocq execution/file-progress events to update binding state.
- **Recommendation**: Connect Lean file-processing/document-version events, retaining general diagnostic notifications and stale-state management.

Position binding, inheritance, locking, caching, and database reads/writes can be retained.
