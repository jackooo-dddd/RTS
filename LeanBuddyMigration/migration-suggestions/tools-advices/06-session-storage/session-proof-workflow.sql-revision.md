# Lean 4 Migration Notes for `session-proof-workflow.sql.ts`

**Purpose**: Define database tables that persist proof-workflow state by session and file.

**1. Persistence Fields | Retain, None**

- **Location**: [Line 5: SessionProofWorkflowTable](../../../prosabuddy-rocq/packages/opencode/src/session/session-proof-workflow.sql.ts#L5).

**Source code to retain** (excerpt):

Workflow payload fields, [From line 11](../../../prosabuddy-rocq/packages/opencode/src/session/session-proof-workflow.sql.ts#L11):

```ts
    file: text().notNull(),
    payload: text().notNull(),
    ...Timestamps,
```

- **Current behavior**: Stores workflow payloads by session/file, with no syntax-specific fields such as Proof/Qed.
- **Recommendation**: Retain the structure and handle Lean fields in workflow payload definitions; changing language does not require rebuilding the table.

No database structure change is inherently required for Coq → Lean migration.
