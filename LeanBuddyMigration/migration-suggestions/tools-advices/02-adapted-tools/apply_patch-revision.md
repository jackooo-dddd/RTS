# Lean 4 Migration Notes for `apply_patch.ts`

**Purpose**: Apply file patches while checking proof regions, target files, and staged-transaction modification constraints.

**1. Coq Guards and Error Hints | Modify, Small**

- **Location**: [Line 203](../../../prosabuddy-rocq/packages/opencode/src/tool/apply_patch.ts#L203).

**Source code to adapt** (only the opening lines or key conditions are shown for long blocks):

Style checks on patch results, [From line 203](../../../prosabuddy-rocq/packages/opencode/src/tool/apply_patch.ts#L203):

```ts
      assertNoRewriteBangInCoqFile(change.movePath ?? change.filePath, change.newContent)
      assertNoIntuitionInCoqFile(change.movePath ?? change.filePath, change.newContent)
```

Coq skill hint branch, [From line 391](../../../prosabuddy-rocq/packages/opencode/src/tool/apply_patch.ts#L391):

```ts
        const skillHints = target.endsWith(".v") ? formatCoqSkillHints(diagnosticText) : ""
        output += `\n\nLSP errors detected in ${path.relative(Instance.worktree, target).replaceAll("\\", "/")}, please fix:\n<diagnostics file="${target}">\n${diagnosticText}${suffix}\n</diagnostics>${skillHints}`
      }
```

- **Current behavior**: Applies Coq style guards to patch results and appends Coq hints to `.v` diagnostics.
- **Recommendation**: Remove SSReflect/intuition guards; use Lean files and corresponding hints in the diagnostic branch.

**2. Regions and Staged Patches | Modify, Medium**

- **Location**: [Line 228](../../../prosabuddy-rocq/packages/opencode/src/tool/apply_patch.ts#L228).

**Related source code** (retain the call or general mechanism and adapt its dependencies):

Proof-boundary checks for patches, [From line 228](../../../prosabuddy-rocq/packages/opencode/src/tool/apply_patch.ts#L228):

```ts
      SessionProofWorkflow.assertBoundProofBodyMutationAllowed({
        sessionID: ctx.sessionID,
        file: change.filePath,
        destinationFile: target,
        before: change.oldContent,
```

- **Current behavior**: Checks modification scope and region ownership, and restricts patch target files and operation types within a transaction.
- **Recommendation**: Retain patch-operation constraints and staging; connect scope checks to Lean declaration/proof-block implementations instead of determining patch validity using Coq Proof/Qed boundaries.

Patch parsing, path checks, diff generation, and batch result aggregation can be retained.
