# Lean 4 Migration Notes for `read.ts`

**Purpose**: Read file contents, preferring staged source not yet written to disk when a proof-edit transaction exists.

**1. Reading Staged Proofs | Retain, None**

- **Location**: [Line 150: stagedSource](../../../prosabuddy-rocq/packages/opencode/src/tool/read.ts#L150).

**Source code to retain** (excerpt):

General staged-source read path, [From line 150](../../../prosabuddy-rocq/packages/opencode/src/tool/read.ts#L150):

```ts
    const stagedSource = ProofEditTransaction.source(ctx.sessionID, filepath)
    const stream = stagedSource !== undefined
      ? Readable.from([stagedSource])
      : createReadStream(filepath, { encoding: "utf8" })
```

- **Current behavior**: Reads transaction source and skips disk-based LSP refresh when staged content exists. This file has no `.v` or Coq proof-syntax checks.
- **Recommendation**: No Lean-specific branch is needed; reuse the same read flow once the dependency layer supports `.lean`.

File reading, chunked output, staged-read synchronization, and read records can all be retained.
