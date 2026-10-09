# Lean 4 Migration Notes for `edit-conflict-guard.ts`

**Purpose**: Check whether the source underlying an edit has changed and provide proof excerpts and other location information on conflicts.

**1. Proof Excerpts in Conflict Messages | Modify, Small**

- **Location**: [Line 26: proofExcerpt](../../../prosabuddy-rocq/packages/opencode/src/tool/edit-conflict-guard.ts#L26).

**Source code to adapt** (only the opening lines or key conditions are shown for long blocks):

Coq entry-point check for proof excerpts, [From line 30](../../../prosabuddy-rocq/packages/opencode/src/tool/edit-conflict-guard.ts#L30):

```ts
    if (lines[index]?.trim() === "Proof.") {
      start = index
      break
    }
```

- **Current behavior**: Searches backward for a standalone `Proof.` line to start the proof excerpt in error messages.
- **Recommendation**: Use the source range of the Lean proof block; retain the general text-window fallback when no range is available, and stop searching for the Proof keyword.

Conflict detection, source hashing, and error reporting can be retained.
