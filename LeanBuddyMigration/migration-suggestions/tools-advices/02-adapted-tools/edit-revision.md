# Lean 4 Migration Notes for `edit.ts`

**Purpose**: Perform text replacements, check proof regions, editing permissions, and style restrictions, and stage proof changes in a transaction.

**1. Style Guards | Remove, Small**

- **Location**: [Line 75](../../../prosabuddy-rocq/packages/opencode/src/tool/edit.ts#L75).

**Source code to adapt** (only the opening lines or key conditions are shown for long blocks):

Style checks in the file-creation branch, [From line 75](../../../prosabuddy-rocq/packages/opencode/src/tool/edit.ts#L75):

```ts
        assertNoRewriteBangInCoqFile(filePath, contentNew)
        assertNoIntuitionInCoqFile(filePath, contentNew)
```

- **Current behavior**: Both creation and replacement paths prohibit SSReflect `rewrite !` and Coq `intuition`.
- **Recommendation**: Remove both guards from the Lean editing path; do not mechanically turn them into a Lean tactic blacklist.

**2. Proof Scope and Transaction Integration | Modify, Medium**

- **Location**: [Line 93](../../../prosabuddy-rocq/packages/opencode/src/tool/edit.ts#L93).

**Related source code** (retain the call or general mechanism and adapt its dependencies):

Proof-body boundary check, [From line 93](../../../prosabuddy-rocq/packages/opencode/src/tool/edit.ts#L93):

```ts
        SessionProofWorkflow.assertBoundProofBodyMutationAllowed({
          sessionID: ctx.sessionID,
          file: filePath,
          before: contentOld,
          after: contentNew,
```

- **Current behavior**: Checks proof scope, lemma order, and region ownership before editing, then calls `ProofEditTransaction.stage`.
- **Recommendation**: Retain the call flow and connect workflow/transaction implementations that calculate scope from Lean declarations and proof blocks. Cover both creation and replacement branches.

**3. Error Hint Branch | Modify, Small**

- **Location**: [Line 287](../../../prosabuddy-rocq/packages/opencode/src/tool/edit.ts#L287).

**Source code to adapt** (only the opening lines or key conditions are shown for long blocks):

Coq skill hint branch, [From line 287](../../../prosabuddy-rocq/packages/opencode/src/tool/edit.ts#L287):

```ts
      const skillHints = filePath.endsWith(".v") ? formatCoqSkillHints(diagnosticText) : ""
      output += `\n\nLSP errors detected in this file, please fix:\n<diagnostics file="${filePath}">\n${diagnosticText}${suffix}\n</diagnostics>${skillHints}`
    }
```

- **Current behavior**: Appends Coq skill hints only to `.v` diagnostics.
- **Recommendation**: Use Lean files and Lean error hints; retain general LSP diagnostic rendering.

Text replacement, diffs, permission checks, conflict handling, and write flow can be retained.
