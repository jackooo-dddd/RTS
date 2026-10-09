# Lean 4 Migration Notes for `multiedit.ts`

**Purpose**: Call the edit tool sequentially for multiple text changes and aggregate their results.

**1. Reusing Edit | Retain, None**

- **Location**: [Line 26: tool](../../../prosabuddy-rocq/packages/opencode/src/tool/multiedit.ts#L26).

**Source code to retain** (excerpt):

Execution entry point reusing edit, [From line 26](../../../prosabuddy-rocq/packages/opencode/src/tool/multiedit.ts#L26):

```ts
    const tool = await EditTool.init()
    const results = []
    for (const [, edit] of params.edits.entries()) {
      const result = await tool.execute(
```

- **Current behavior**: Calls `EditTool.execute` for each edit and forwards region takeover parameters; it has no independent Coq checks.
- **Recommendation**: Let `edit.ts` and its dependencies handle Lean adaptation; this file has no separate migration points.

The tool's loop, parameter forwarding, and result aggregation can all be retained.
