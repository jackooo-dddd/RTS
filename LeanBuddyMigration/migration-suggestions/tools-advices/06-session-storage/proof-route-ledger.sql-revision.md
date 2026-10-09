# Lean 4 Migration Notes for `proof-route-ledger.sql.ts`

**Purpose**: Define database tables for proof-route failure records, context fingerprints, and evidence payloads.

**1. Persistence Fields | Retain, None**

- **Location**: [Line 4: ProofRouteFailureTable](../../../prosabuddy-rocq/packages/opencode/src/session/proof-route-ledger.sql.ts#L4).

**Source code to retain** (excerpt):

Route and context fingerprint fields, [From line 9](../../../prosabuddy-rocq/packages/opencode/src/session/proof-route-ledger.sql.ts#L9):

```ts
    file: text().notNull(),
    theorem: text().notNull(),
    theorem_context_fingerprint: text().notNull(),
    semantic_fingerprint: text().notNull(),
    confidence: text().notNull(),
    status: text().notNull(),
    payload: text().notNull(),
```

- **Current behavior**: Stores context/semantic fingerprints and failure payloads without restricting the proof language.
- **Recommendation**: Retain the table structure; handle Lean fingerprint algorithms and legacy-record compatibility in the ledger layer.

No database structure change is inherently required for Coq → Lean migration.
