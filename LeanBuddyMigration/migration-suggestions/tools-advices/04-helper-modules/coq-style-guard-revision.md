# Lean 4 Migration Notes for `coq-style-guard.ts`

**Purpose**: Check Coq proof text and reject specified SSReflect repeat-rewrite syntax and the intuition tactic.

**1. SSReflect and Intuition Rules | Remove, Small**

- **Location**: [Line 1: REWRITE_BANG_PATTERN](../../../prosabuddy-rocq/packages/opencode/src/tool/coq-style-guard.ts#L1).

**Source code to adapt** (only the opening lines or key conditions are shown for long blocks):

SSReflect repeat-rewrite matching, [Line 1](../../../prosabuddy-rocq/packages/opencode/src/tool/coq-style-guard.ts#L1):

```ts
export const REWRITE_BANG_PATTERN = /\brewrite\b[^.]*[-+]?!\s*(?:[A-Za-z_/(\\]|(?=\.|$))/
```

Intuition matching, [Line 20](../../../prosabuddy-rocq/packages/opencode/src/tool/coq-style-guard.ts#L20):

```ts
export const INTUITION_PATTERN = /\bintuition\b/
```

Wrapper restricted to Coq files, [From line 15](../../../prosabuddy-rocq/packages/opencode/src/tool/coq-style-guard.ts#L15):

```ts
export function assertNoRewriteBangInCoqFile(filePath: string, content: string) {
  if (!filePath.endsWith(".v")) return
  assertNoRewriteBang(content, `Coq file ${filePath}`)
}
```

- **Current behavior**: Prohibits `rewrite !`/`rewrite -!` and `intuition`; file-level wrappers check only `.v` files.
- **Recommendation**: Remove these rules and wrappers from Lean call paths; if retaining Rocq compatibility, keep them only in the Rocq backend rather than copying them into Lean tactic bans.

The Lean version does not need these Coq tactic restrictions.
