# Lean 4 Migration Notes for `proof-edit-transaction.sql.ts`

**Purpose**: Define database tables for proof-edit transactions, source revisions, and related payloads.

**1. Persistence Fields | Retain, None**

- **Location**: [Line 4: ProofEditTransactionTable](../../../prosabuddy-rocq/packages/opencode/src/session/proof-edit-transaction.sql.ts#L4).

**Source code to retain** (excerpt):

General transaction persistence fields, [From line 9](../../../prosabuddy-rocq/packages/opencode/src/session/proof-edit-transaction.sql.ts#L9):

```ts
    file: text().notNull(),
    theorem: text().notNull(),
    scope_key: text().notNull(),
    status: text().notNull(),
    payload: text().notNull(),
```

- **Current behavior**: Two tables store transactions, revisions, source/hashes, and payloads without Coq syntax constraints.
- **Recommendation**: Retain the table structures; represent Lean state in the payload's schema first, and perform a database migration only when new standalone persistent fields are actually required.

No database structure change is inherently required for Coq → Lean migration.
