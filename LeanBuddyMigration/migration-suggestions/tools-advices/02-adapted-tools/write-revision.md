# Lean 4 Migration Notes for `write.ts`

**Purpose**: Write complete file contents, checking proof scope and transaction constraints to decide whether to stage changes or write them to disk.

**1. Coq Style Restrictions | Remove, Small**

- **Location**: [Line 39](../../../prosabuddy-rocq/packages/opencode/src/tool/write.ts#L39).

**Source code to adapt** (only the opening lines or key conditions are shown for long blocks):

Pre-write style checks, [From line 39](../../../prosabuddy-rocq/packages/opencode/src/tool/write.ts#L39):

```ts
    assertNoRewriteBangInCoqFile(filepath, params.content)
    assertNoIntuitionInCoqFile(filepath, params.content)
```

- **Current behavior**: Calls two Coq tactic guards before writing.
- **Recommendation**: Remove calls to `assertNoRewriteBangInCoqFile` and `assertNoIntuitionInCoqFile` from the Lean path.

**2. Theorem/Region Restrictions | Modify, Medium**

- **Location**: [Line 57](../../../prosabuddy-rocq/packages/opencode/src/tool/write.ts#L57).

**Related source code** (retain the call or general mechanism and adapt its dependencies):

Proof-boundary check entry point, [From line 57](../../../prosabuddy-rocq/packages/opencode/src/tool/write.ts#L57):

```ts
    SessionProofWorkflow.assertBoundProofBodyMutationAllowed({
      sessionID: ctx.sessionID,
      file: filepath,
      before: contentOld,
      after: params.content,
```

- **Current behavior**: Checks proof scope through the workflow and uses `ProofEditTransaction.stage` to decide between staging and disk writes; this file does not parse Coq theorems itself.
- **Recommendation**: Retain these calls; dependencies should return Lean proof ranges and ensure that whole-file replacement still cannot exceed the authorized Lean proof block.

Whole-file writing, diffs, file events, transaction staging, and general LSP feedback can all be retained.
